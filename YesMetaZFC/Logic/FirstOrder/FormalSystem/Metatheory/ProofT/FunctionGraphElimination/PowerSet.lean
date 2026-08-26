import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Hilbert
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.PowerSet

/-!
# 幂集函数图消去实例

幂集函数使用已有 `power_set_spec` 作为图公式。该实例只登记语法编译器真正消费的
sort、scope 与目标函数消失证书；全体性和单值性继续由 `power_set_exists_derives`
与 `power_set_unique` 在后续证明等价层消费。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace FunctionGraphElimination
namespace PowerSet

open Nonlogical.BasicSetTheory
open scoped Symbols

set_option autoImplicit false

/-- 一元幂集图；错误元数仅作为不可达的良构性外分支落到假。 -/
def graph : List SetTerm → SetTerm → SetFormula
  | (source :: []), result =>
      power_set_spec source result
  | _, _ =>
      .falsum

private theorem push_scoped
    {scope : Scope signature} {term : SetTerm}
    (hTerm : TermScoped scope term) :
    TermScoped (Scope.push scope SetSort.set) term := by
  apply Term.scoped_mono hTerm
  intro sort
  cases sort
  simp [Scope.push]

private theorem graph_well_formed
    {arguments : List SetTerm} {result : SetTerm}
    (hArguments :
      ArgsWellSorted arguments
        (signature.funcDomain
          FunctionSymbol.powerSet))
    (hResult :
      TermWellSorted result SetSort.set) :
    FormulaWellFormed (graph arguments result) := by
  change ArgsWellSorted arguments [SetSort.set]
    at hArguments
  cases hArguments with
  | cons hSource hTail =>
      cases hTail
      unfold graph power_set_spec
      apply FormulaWellFormed.forallE
      apply FormulaWellFormed.iff
      · apply FormulaWellFormed.rel
        simpa [signature] using
          ArgsWellSorted.cons
            (TermWellSorted.bvar
              SetSort.set 0)
            (ArgsWellSorted.cons hResult
              ArgsWellSorted.nil)
      · apply FormulaWellFormed.rel
        simpa [signature] using
          ArgsWellSorted.cons
            (TermWellSorted.bvar
              SetSort.set 0)
            (ArgsWellSorted.cons hSource
              ArgsWellSorted.nil)

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
      change FormulaScoped scope Formula.falsum
      exact .falsum
  | cons source tail =>
      cases tail with
      | nil =>
          unfold graph power_set_spec
          apply FormulaScoped.forallE
          exact .iff
            (FormulaScoped.rel
              (σ := signature)
              RelationSymbol.membership
              [Term.var (.bvar SetSort.set 0), result] <| by
              intro term hTerm
              rcases List.mem_cons.mp hTerm with
                rfl | hTerm
              · exact TermScoped.bvar <| by
                  simp [Scope.push]
              · rcases List.mem_singleton.mp hTerm with rfl
                exact push_scoped hResult)
            (FormulaScoped.rel
              (σ := signature)
              RelationSymbol.subset
              [Term.var (.bvar SetSort.set 0), source] <| by
              intro term hTerm
              rcases List.mem_cons.mp hTerm with
                rfl | hTerm
              · exact TermScoped.bvar <| by
                  simp [Scope.push]
              · exact push_scoped <|
                  hArguments term hTerm)
      | cons second rest =>
          change FormulaScoped scope Formula.falsum
          exact .falsum

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
      simp [graph, Formula.freeSupport] at hMember
  | cons source tail =>
      cases tail with
      | nil =>
          simpa [graph, power_set_spec,
            Formula.freeSupport,
            Term.freeSupportList,
            Term.freeSupport, or_comm] using
              hMember
      | cons second rest =>
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
      rfl
  | cons source tail =>
      cases tail with
      | nil =>
          cases target
          simp [graph, power_set_spec,
            Formula.substituteFree,
            Term.substituteFree]
      | cons second rest =>
          rfl

private theorem graph_avoids
    {arguments : List SetTerm} {result : SetTerm}
    (hArguments :
      TermsAvoid FunctionSymbol.powerSet arguments)
    (hResult :
      TermAvoids FunctionSymbol.powerSet result) :
    FormulaAvoids FunctionSymbol.powerSet
      (graph arguments result) := by
  cases arguments with
  | nil =>
      change True
      trivial
  | cons source tail =>
      cases tail with
      | nil =>
          change
            TermsAvoid FunctionSymbol.powerSet
                [Term.var (.bvar SetSort.set 0), result] ∧
              TermsAvoid FunctionSymbol.powerSet
                [Term.var (.bvar SetSort.set 0), source]
          exact ⟨
            (by
              intro term hTerm
              rcases List.mem_cons.mp hTerm with
                rfl | hTerm
              · simp [TermAvoids]
              · rw [List.mem_singleton.mp hTerm]
                exact hResult),
            (by
              intro term hTerm
              rcases List.mem_cons.mp hTerm with
                rfl | hTerm
              · simp [TermAvoids]
              · rw [List.mem_singleton.mp hTerm]
                exact hArguments source (by simp))⟩
      | cons second rest =>
          change True
          trivial

/-- 已实现的幂集函数图消去数据。 -/
def data : Data signature where
  symbol := FunctionSymbol.powerSet
  sort := SetSort.set
  codomain_eq := rfl
  graph := PowerSet.graph
  graph_well_formed := graph_well_formed
  graph_scoped := graph_scoped
  graph_freeSupport := graph_freeSupport
  graph_substituteFree := graph_substituteFree
  graph_avoids := graph_avoids

private theorem singleton_admissible
    {arguments : List SetTerm}
    (hArguments :
      ArgsAdmissible arguments [SetSort.set]) :
    ∃ source,
      arguments = [source] ∧
        Term.Admissible source SetSort.set := by
  rcases hArguments with ⟨hSorted, hScoped⟩
  cases hSorted with
  | cons hSource hTail =>
      cases hTail
      exact ⟨_, rfl, hSource,
        hScoped _ (by simp)⟩

private theorem total
    {arguments : List SetTerm}
    (resultId : FreeVarId)
    (hArguments :
      ArgsAdmissible arguments
        (signature.funcDomain
          FunctionSymbol.powerSet))
    (hFresh :
      (SetSort.set, resultId) ∉
        Term.freeSupportList arguments) :
    Derives power_set_theory [] <|
      Formula.existsE SetSort.set <|
        Formula.closeFreeAt SetSort.set resultId 0 <|
          graph arguments <|
            .var (.fvar SetSort.set resultId) := by
  change ArgsAdmissible arguments [SetSort.set]
    at hArguments
  rcases singleton_admissible hArguments with
    ⟨source, rfl, hSource⟩
  have hSourceFresh :
      (SetSort.set, resultId) ∉
        Term.freeSupport source := by
    simpa [Term.freeSupportList] using hFresh
  have hSourceClose :
      Term.closeFreeAt SetSort.set resultId 1 source =
        source :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set resultId 1 source hSource.2
        hSourceFresh
  simpa [graph, power_set_exists, power_set_spec,
    Formula.closeFreeAt, Formula.next_depth,
    Term.closeFreeAt,
    hSourceClose] using
    power_set_exists_derives source hSource

private theorem functional
    {arguments : List SetTerm}
    {left right : SetTerm}
    (hArguments :
      ArgsAdmissible arguments
        (signature.funcDomain
          FunctionSymbol.powerSet))
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    Derives power_set_theory [] <|
      Formula.imp (graph arguments left) <|
        Formula.imp (graph arguments right) <|
          Formula.equal left right := by
  change ArgsAdmissible arguments [SetSort.set]
    at hArguments
  rcases singleton_admissible hArguments with
    ⟨source, rfl, hSource⟩
  apply FirstOrder.Derives.theory_weaken
    (T := extensionality_theory)
  · intro φ hφ
    exact Or.inr (Or.inr hφ)
  · simpa [graph] using
      power_set_unique source left right
        hSource hLeft hRight

/-- 幂集存在理论给出的全体、单值函数图表示。 -/
def graph_presentation : GraphPresentation data where
  theory := power_set_theory
  theory_sentence := by
    intro φ hφ
    exact power_set_operator_theory_sentence
      (Or.inr hφ)
  total := total
  functional := functional

/-- 打开幂集规格量词后的源层逐元素公式。 -/
private def definition_point : SetFormula :=
  (x#1 ∈ₘ 𝒫ₘ(x#0)) ↔ₘ
    (x#1 ⊆ₘ x#0)

/-- 逐元素公式消去幂集函数项后的显式图正规形。 -/
private def compiled_definition_point : SetFormula :=
  ((∃ₘ[SetSort.set, 0],
      power_set_spec (x#1) (x#0) ∧ₘ
        (x#3 ∈ₘ x#0)) ↔ₘ
    (x#3 ⊆ₘ x#1))

/-- 逐元素公式的编译只生成一个偶数图见证。 -/
private theorem formula_definition_point :
    FunctionGraphElimination.formula
        data definition_point =
      compiled_definition_point := by
  simp [definition_point,
    compiled_definition_point,
    FunctionGraphElimination.formula,
    FunctionGraphElimination.relation,
    FunctionGraphElimination.terms,
    FunctionGraphElimination.term,
    close_witnesses, condition_conjunction,
    data, graph, source_id, witness_id]

/-- 幂集存在理论中的任意公理不含待消去函数，故编译后严格保持不变。 -/
private theorem formula_base_eq
    {source : SetFormula}
    (hSource : power_set_theory source) :
    FunctionGraphElimination.formula data source =
      source := by
  apply formula_eq_of_sentence_avoids
    data source
  · change
      source = power_set_axiom ∨
        (source = subset_definition_axiom ∨
          extensionality_theory source)
      at hSource
    rcases hSource with rfl | hSource
    · simpa [power_set_axiom] using
        formula_avoids_closeFreeAt
          FunctionSymbol.powerSet
          SetSort.set 0 0
          (power_set_exists (x#0)) <| by
            simp [power_set_exists,
              FormulaAvoids, TermsAvoid,
              TermAvoids]
    · rcases hSource with rfl | hSource
      · simpa [subset_definition_axiom] using
          formula_avoids_forall_close
            FunctionSymbol.powerSet
            [(SetSort.set, 0),
              (SetSort.set, 1)]
            (subset_definition_instance
              (x#0) (x#1)) <| by
                simp [subset_definition_instance,
                  subset_condition,
                  FormulaAvoids, TermsAvoid,
                  TermAvoids]
      · change source = extensionality_axiom
          at hSource
        subst source
        simpa [extensionality_axiom] using
          formula_avoids_forall_close
            FunctionSymbol.powerSet
            [(SetSort.set, 0),
              (SetSort.set, 1)]
            (extensionality_instance
              (x#0) (x#1)) <| by
                simp [extensionality_instance,
                  agreement_to_equality,
                  membership_agreement,
                  FormulaAvoids, TermsAvoid,
                  TermAvoids]
  · exact graph_presentation.theory_sentence
      hSource

/-- 幂集存在理论是闭句理论，因而所有证明级 eigenvariable 均对理论新鲜。 -/
private theorem theory_fresh
    (id : FreeVarId) :
    ∀ source, power_set_theory source →
      (SetSort.set, id) ∉
        Formula.freeSupport source := by
  intro source hSource
  rw [(graph_presentation.theory_sentence
    hSource).2]
  exact List.not_mem_nil

/-- 幂集存在性逐点证明编译后的定义公式。 -/
private theorem compiled_definition_point_derives :
    Derives power_set_theory []
      compiled_definition_point := by
  unfold compiled_definition_point
  apply Derives.iff_intro
  ·
    let body :=
      Formula.conj
        (power_set_spec (x#1) (x#0))
        (x#3 ∈ₘ x#0)
    apply Derives.exists_elim
        (sort := SetSort.set)
        (eigen := 0)
        (body := body)
    · exact theory_fresh 0
    · intro source hSource
      rcases List.mem_singleton.mp hSource with rfl
      simpa [Formula.freeSupport] using
        Formula.not_mem_freeSupport_closeFreeAt
          SetSort.set 0 0 body
    · native_decide
    · simpa [body] using
        (Derives.assumption_of_mem
          (by simp) :
          Derives power_set_theory
            [∃ₘ[SetSort.set, 0], body]
            (∃ₘ[SetSort.set, 0], body))
    · have hBody :
          Derives power_set_theory
            [body,
              ∃ₘ[SetSort.set, 0], body]
            body :=
        Derives.assumption_of_mem
          (by simp)
      have hSpec :=
        Derives.conj_elim_left hBody
      have hMember :=
        Derives.conj_elim_right hBody
      have hAtRaw :=
        Derives.forall_elim
          (term := x#3) hSpec
      have hAt :
          Derives power_set_theory
            [body,
              ∃ₘ[SetSort.set, 0], body]
            ((x#3 ∈ₘ x#0) ↔ₘ
              (x#3 ⊆ₘ x#1)) := by
        simpa [body, power_set_spec,
          Formula.openAt, Term.openAt,
          set_variable] using hAtRaw
      exact Derives.iff_elim_right
        hAt hMember
  ·
    let graphBody :=
      power_set_spec (x#1) (x#0)
    have hArguments :
        ArgsAdmissible [x#1]
          [SetSort.set] := by
      exact ArgsAdmissible.cons
        (set_variable_admissible 1)
        ArgsAdmissible.nil
    have hExists :
        Derives power_set_theory
          [x#3 ⊆ₘ x#1]
          (Formula.existsE SetSort.set
            (Formula.closeFreeAt
              SetSort.set 0 0 graphBody)) := by
      have hBase :=
        graph_presentation.total
          0 hArguments (by
            simp [Term.freeSupportList,
              Term.freeSupport])
      simpa [graph, graphBody] using
        hBase.context_weaken_cons
    apply graph_presentation.exists_conj_of_case
    · intro source hSource
      rcases List.mem_singleton.mp hSource with rfl
      native_decide
    · exact hExists
    · have hSpec :
          Derives power_set_theory
            [graphBody, x#3 ⊆ₘ x#1]
            graphBody :=
        Derives.assumption_of_mem
          (by simp)
      have hSubset :
          Derives power_set_theory
            [graphBody, x#3 ⊆ₘ x#1]
            (x#3 ⊆ₘ x#1) :=
        Derives.assumption_of_mem
          (by simp)
      have hAtRaw :=
        Derives.forall_elim
          (term := x#3) hSpec
      have hAt :
          Derives power_set_theory
            [graphBody, x#3 ⊆ₘ x#1]
            ((x#3 ∈ₘ x#0) ↔ₘ
              (x#3 ⊆ₘ x#1)) := by
        simpa [graphBody, power_set_spec,
          Formula.openAt, Term.openAt,
          set_variable] using hAtRaw
      exact Derives.iff_elim_left
        hAt hSubset

/-- 幂集存在理论证明开放定义实例的函数图编译。 -/
private theorem formula_definition_instance_derives :
    Derives power_set_theory []
      (FunctionGraphElimination.formula data
        (power_set_definition_instance
          (x#0))) := by
  have hPoint :
      Derives power_set_theory []
        (FunctionGraphElimination.formula
          data definition_point) := by
    rw [formula_definition_point]
    exact compiled_definition_point_derives
  have hElement :
      Derives power_set_theory []
        (Formula.forallE SetSort.set
          (Formula.closeFreeAt SetSort.set
            (source_id 1) 0
            (FunctionGraphElimination.formula
              data definition_point))) := by
    apply Derives.forall_intro
    · exact theory_fresh (source_id 1)
    · intro source hSource
      cases hSource
    · exact hPoint
  let body : SetFormula :=
    (bₛ#0 ∈ₘ 𝒫ₘ(x#0)) ↔ₘ
      (bₛ#0 ⊆ₘ x#0)
  have hForall :
      Formula.Admissible
        (Formula.forallE SetSort.set body) := by
    simpa [body, power_set_definition_instance,
      power_set_spec] using
      power_set_definition_instance_admissible
        (set_variable_admissible 0)
  have hNormalized :=
    graph_presentation.formula_forall_iff_at
      SetSort.set body hForall 1 (by
        native_decide)
  apply Derives.iff_elim_left hNormalized
  simpa [body, definition_point,
    Formula.openAt, Term.openAt,
    set_variable] using hElement

/-- 幂集存在理论证明整个定义公理的函数图编译。 -/
private theorem formula_definition_axiom_derives :
    Derives power_set_theory []
      (FunctionGraphElimination.formula
        data power_set_definition_axiom) := by
  have hSource :
      Derives power_set_theory []
        (Formula.forallE SetSort.set
          (Formula.closeFreeAt SetSort.set
            (source_id 0) 0
            (FunctionGraphElimination.formula
              data
              (power_set_definition_instance
                (x#0))))) := by
    apply Derives.forall_intro
    · exact theory_fresh (source_id 0)
    · intro source hSource
      cases hSource
    · exact formula_definition_instance_derives
  have hInstance :
      Formula.Admissible
        (power_set_definition_instance
          (x#0)) :=
    power_set_definition_instance_admissible
      (set_variable_admissible 0)
  have hNormalized :=
    graph_presentation.formula_forall_close_iff
      SetSort.set 0
      (power_set_definition_instance
        (x#0)) hInstance
  apply Derives.iff_elim_left hNormalized
  simpa [power_set_definition_axiom] using hSource

/-- 幂集函数扩张的每条公理均可在幂集存在理论中消去函数图。 -/
private theorem compile_axiom
    {source : SetFormula}
    (hSource :
      power_set_operator_theory source) :
    Derives power_set_theory []
      (FunctionGraphElimination.formula
        data source) := by
  rcases hSource with rfl | hSource
  · exact formula_definition_axiom_derives
  · rw [formula_base_eq hSource]
    exact Derives.theory_mem hSource
      (hFormulaCheck :=
        Formula.check_certificate_of_admissible
          (power_set_theory_admissible
            source hSource))

/-- 幂集函数扩张的理论级函数图消去表示。 -/
def theory_presentation :
    TheoryPresentation data where
  graph := graph_presentation
  source := power_set_operator_theory
  compile_axiom := compile_axiom

/-- 幂集函数扩张的 Hilbert 证明可整体翻译到幂集存在理论。 -/
theorem hilbert
    {source : SetFormula}
    (hSource :
      HilbertDerives
        power_set_operator_theory source) :
    Derives power_set_theory []
      (FunctionGraphElimination.formula
        data source) :=
  theory_presentation.hilbert hSource

/-- 幂集函数扩张的 checked 自然演绎证明可整体翻译到幂集存在理论。 -/
theorem derives
    {source : SetFormula}
    (hSource :
      Derives power_set_operator_theory []
        source) :
    Derives power_set_theory []
      (FunctionGraphElimination.formula
        data source) :=
  theory_presentation.derives
    SetSort.set hSource

/-- 幂集函数扩张中的 Hilbert 矛盾回传为幂集存在理论矛盾。 -/
theorem hilbert_falsum
    (hSource :
      HilbertDerives
        power_set_operator_theory
        Formula.falsum) :
    Derives power_set_theory []
      Formula.falsum := by
  exact theory_presentation.hilbert_falsum
    hSource

/-- 幂集函数扩张中的 checked 矛盾回传为幂集存在理论矛盾。 -/
theorem derives_falsum
    (hSource :
      Derives power_set_operator_theory []
        Formula.falsum) :
    Derives power_set_theory []
      Formula.falsum :=
  theory_presentation.derives_falsum
    SetSort.set hSource

/-- 幂集存在理论一致时，其函数符号定义扩张保持 checked 一致。 -/
theorem consistent
    (hBase :
      Derives.Consistent
        power_set_theory []) :
    Derives.Consistent
      power_set_operator_theory [] :=
  theory_presentation.consistent
    SetSort.set hBase

/-- 幂集存在理论一致时，其函数符号定义扩张保持 Hilbert 一致。 -/
theorem hilbert_consistent
    (hBase :
      Derives.Consistent
        power_set_theory []) :
    ¬ HilbertDerives
        power_set_operator_theory
        Formula.falsum :=
  theory_presentation.hilbert_consistent hBase

private theorem realizes
    {arguments : List SetTerm}
    (hArguments :
      ArgsAdmissible arguments
        (signature.funcDomain
          FunctionSymbol.powerSet)) :
    Derives power_set_operator_theory [] <|
      graph arguments
        (.app FunctionSymbol.powerSet arguments) := by
  change ArgsAdmissible arguments [SetSort.set]
    at hArguments
  rcases singleton_admissible hArguments with
    ⟨source, rfl, hSource⟩
  simpa [graph, power_set_term] using
    power_set_term_spec_derives source hSource

/-- 幂集函数定义扩张的完整函数图表示。 -/
def presentation : DefinitionPresentation data where
  toGraphPresentation := graph_presentation
  extension := power_set_operator_theory
  extension_sentence :=
    power_set_operator_theory_sentence
  base_subset := by
    intro φ hφ
    exact Or.inr hφ
  realizes := realizes

/-- 幂集函数图编译与原闭句在幂集运算符理论中等价。 -/
theorem sentence_iff
    {source : SetFormula}
    (hSource : Formula.Sentence source) :
    Derives power_set_operator_theory []
      (Formula.iff
        (FunctionGraphElimination.formula
          data source)
        source) :=
  presentation.sentence_iff hSource

/--
幂集运算符理论中的闭句独立性，反射为幂集存在理论中编译闭句的独立性。
-/
theorem reflects_independence
    {source : SetFormula}
    (hSource : Formula.Sentence source)
    (hIndependent :
      (¬ Derives power_set_operator_theory []
          source) ∧
        (¬ Derives power_set_operator_theory []
          (Formula.neg source))) :
    (¬ Derives power_set_theory []
        (FunctionGraphElimination.formula
          data source)) ∧
      (¬ Derives power_set_theory []
        (Formula.neg
          (FunctionGraphElimination.formula
            data source))) :=
  presentation.reflects_independence
    hSource hIndependent

end PowerSet
end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
