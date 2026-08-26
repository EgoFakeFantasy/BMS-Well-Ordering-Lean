import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.UnorderedPair

/-!
# 单点集函数图消去实例

单点集函数以 `singleton_spec` 为图，目标理论保留无序对函数。存在性由重复元素的
配对给出，单值性只使用外延性；因此该步骤可直接串接无序对消去实例。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace FunctionGraphElimination
namespace Singleton

open Nonlogical.BasicSetTheory
open scoped Symbols

set_option autoImplicit false

/-- 一元单点集图；错误元数在良构分支外落到假。 -/
def graph : List SetTerm → SetTerm → SetFormula
  | (element :: []), result =>
      singleton_spec element result
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
          FunctionSymbol.singleton))
    (hResult :
      TermWellSorted result SetSort.set) :
    FormulaWellFormed (graph arguments result) := by
  change ArgsWellSorted arguments [SetSort.set]
    at hArguments
  cases hArguments with
  | cons hElement hNil =>
      cases hNil
      unfold graph singleton_spec
      apply FormulaWellFormed.forallE
      apply FormulaWellFormed.iff
      · apply FormulaWellFormed.rel
        simpa [signature] using
          ArgsWellSorted.cons
            (TermWellSorted.bvar
              SetSort.set 0)
            (ArgsWellSorted.cons hResult
              ArgsWellSorted.nil)
      · exact FormulaWellFormed.equal
          (TermWellSorted.bvar
            (σ := signature)
            SetSort.set 0)
          hElement

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
      simpa [graph] using
        (FormulaScoped.falsum :
          FormulaScoped scope
            (Formula.falsum : SetFormula))
  | cons element tail =>
      cases tail with
      | nil =>
          unfold graph singleton_spec
          apply FormulaScoped.forallE
          apply FormulaScoped.iff
          · exact FormulaScoped.rel
              (σ := signature)
              RelationSymbol.membership
              [(Term.var
                  (.bvar SetSort.set 0) :
                    SetTerm),
                result] <| by
                intro term hTerm
                rcases List.mem_cons.mp hTerm with
                  rfl | hTerm
                · exact TermScoped.bvar
                    (σ := signature)
                    (ctx :=
                      Scope.push scope
                        SetSort.set)
                    (Nat.zero_lt_succ _)
                · rw [List.mem_singleton.mp
                    hTerm]
                  exact push_scoped hResult
          · exact FormulaScoped.equal
              (TermScoped.bvar
                (σ := signature) <| by
                  change
                    0 < Nat.succ
                      (scope SetSort.set)
                  exact Nat.zero_lt_succ _)
              (push_scoped <|
                hArguments element (by simp))
      | cons extra rest =>
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
      simp [graph, Formula.freeSupport] at hMember
  | cons element tail =>
      cases tail with
      | nil =>
          simpa [graph, singleton_spec,
            Formula.freeSupport,
            Term.freeSupportList,
            Term.freeSupport, or_comm] using
              hMember
      | cons extra rest =>
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
      simp [graph, Formula.substituteFree]
  | cons element tail =>
      cases tail with
      | nil =>
          cases target
          simp [graph, singleton_spec,
            Formula.substituteFree,
            Term.substituteFree]
      | cons extra rest =>
          simp [graph, Formula.substituteFree]

private theorem graph_avoids
    {arguments : List SetTerm} {result : SetTerm}
    (hArguments :
      TermsAvoid FunctionSymbol.singleton arguments)
    (hResult :
      TermAvoids FunctionSymbol.singleton result) :
    FormulaAvoids FunctionSymbol.singleton
      (graph arguments result) := by
  cases arguments with
  | nil =>
      simp [graph, FormulaAvoids]
  | cons element tail =>
      cases tail with
      | nil =>
          change
            TermsAvoid FunctionSymbol.singleton
                [(Term.var
                    (.bvar SetSort.set 0) :
                      SetTerm),
                  result] ∧
              (TermAvoids FunctionSymbol.singleton
                  (Term.var
                    (.bvar SetSort.set 0) :
                      SetTerm) ∧
                TermAvoids FunctionSymbol.singleton
                  element)
          have hElement :=
            hArguments element (by simp)
          simp [TermsAvoid, TermAvoids,
            hResult, hElement]
      | cons extra rest =>
          simp [graph, FormulaAvoids]

/-- 已实现的单点集函数图消去数据。 -/
def data : Data signature where
  symbol := FunctionSymbol.singleton
  sort := SetSort.set
  codomain_eq := rfl
  graph := Singleton.graph
  graph_well_formed := graph_well_formed
  graph_scoped := graph_scoped
  graph_freeSupport := graph_freeSupport
  graph_substituteFree := graph_substituteFree
  graph_avoids := graph_avoids

private theorem singleton_admissible
    {arguments : List SetTerm}
    (hArguments :
      ArgsAdmissible arguments [SetSort.set]) :
    ∃ element,
      arguments = [element] ∧
        Term.Admissible element SetSort.set := by
  rcases hArguments with
    ⟨hSorted, hScoped⟩
  cases hSorted with
  | cons hElement hNil =>
      cases hNil
      exact ⟨_, rfl, hElement,
        hScoped _ (by simp)⟩

private theorem total
    {arguments : List SetTerm}
    (resultId : FreeVarId)
    (hArguments :
      ArgsAdmissible arguments
        (signature.funcDomain
          FunctionSymbol.singleton))
    (hFresh :
      (SetSort.set, resultId) ∉
        Term.freeSupportList arguments) :
    Derives pairing_operator_theory [] <|
      Formula.existsE SetSort.set <|
        Formula.closeFreeAt SetSort.set resultId 0 <|
          graph arguments <|
            .var (.fvar SetSort.set resultId) := by
  change ArgsAdmissible arguments [SetSort.set]
    at hArguments
  rcases singleton_admissible hArguments with
    ⟨element, rfl, hElement⟩
  have hElementFresh :
      (SetSort.set, resultId) ∉
        Term.freeSupport element := by
    simpa [Term.freeSupportList] using hFresh
  have hElementClose :
      Term.closeFreeAt SetSort.set resultId 1
          element =
        element :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set resultId 1 element
      hElement.2 hElementFresh
  have hExists :
      Derives pairing_operator_theory []
        (singleton_exists element) :=
    Derives.theory_weaken
      (T := pairing_theory)
      (U := pairing_operator_theory)
      (fun _ hφ => Or.inr hφ)
      (singleton_exists_derives
        element hElement)
  simpa [graph, singleton_exists,
    singleton_spec,
    Formula.closeFreeAt, Formula.next_depth,
    Term.closeFreeAt, hElementClose] using
      hExists

private theorem functional
    {arguments : List SetTerm}
    {left right : SetTerm}
    (hArguments :
      ArgsAdmissible arguments
        (signature.funcDomain
          FunctionSymbol.singleton))
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    Derives pairing_operator_theory [] <|
      Formula.imp (graph arguments left) <|
        Formula.imp (graph arguments right) <|
          Formula.equal left right := by
  change ArgsAdmissible arguments [SetSort.set]
    at hArguments
  rcases singleton_admissible hArguments with
    ⟨element, rfl, hElement⟩
  apply Derives.theory_weaken
    (T := extensionality_theory)
  · intro φ hφ
    exact Or.inr (Or.inr hφ)
  · simpa [graph, singleton_spec,
      membership_specification] using
      membership_specification_unique
        left right (bₛ#0 ≐ₘ element)
        hLeft hRight
        (singleton_spec_admissible
          hElement hLeft)
        (singleton_spec_admissible
          hElement hRight)

/-- 无序对函数理论给出的全体、单值单点集图表示。 -/
def graph_presentation : GraphPresentation data where
  theory := pairing_operator_theory
  theory_sentence := by
    intro φ hφ
    exact pairing_operator_theory_sentence hφ
  total := total
  functional := functional

/-- 外层 binder 打开后的单点集定义实例。 -/
private def definition_point : SetFormula :=
  singleton_definition_instance (x#0)

/-- 开放定义实例消去单点集函数后的显式图正规形。 -/
private def compiled_definition_point : SetFormula :=
  ∃ₘ[SetSort.set, 0],
    singleton_spec (x#1) (x#0) ∧ₘ
      ((x#0) ≐ₘ
        unordered_pair_term (x#1) (x#1))

/-- 开放单点集定义实例的编译只生成一个偶数图见证。 -/
private theorem formula_definition_point :
    FunctionGraphElimination.formula
        data definition_point =
      compiled_definition_point := by
  simp [definition_point,
    compiled_definition_point,
    singleton_definition_instance,
    FunctionGraphElimination.formula,
    FunctionGraphElimination.equality,
    FunctionGraphElimination.terms,
    FunctionGraphElimination.term,
    close_witnesses, condition_conjunction,
    data, graph, source_id, witness_id,
    singleton_term, unordered_pair_term]

private theorem theory_fresh
    (id : FreeVarId) :
    ∀ source, pairing_operator_theory source →
      (SetSort.set, id) ∉
        Formula.freeSupport source := by
  intro source hSource
  rw [(graph_presentation.theory_sentence
    hSource).2]
  exact List.not_mem_nil

/-- 无序对函数理论证明编译后的开放单点集定义。 -/
private theorem compiled_definition_point_derives :
    Derives pairing_operator_theory []
      compiled_definition_point := by
  unfold compiled_definition_point
  let arguments : List SetTerm := [x#1]
  let pair := unordered_pair_term (x#1) (x#1)
  let graphBody := singleton_spec (x#1) (x#0)
  have hArguments :
      ArgsAdmissible arguments [SetSort.set] :=
    ArgsAdmissible.cons
      (set_variable_admissible 1)
      ArgsAdmissible.nil
  have hZero :
      Term.Admissible (x#0) SetSort.set :=
    set_variable_admissible 0
  have hPair :
      Term.Admissible pair SetSort.set := by
    exact unordered_pair_term_admissible
      (x#1) (x#1)
      (set_variable_admissible 1)
      (set_variable_admissible 1)
  have hExists :
      Derives pairing_operator_theory []
        (Formula.existsE SetSort.set
          (Formula.closeFreeAt
            SetSort.set 0 0 graphBody)) := by
    have hBase :=
      graph_presentation.total
        0 hArguments (by
          simp [arguments,
            Term.freeSupportList,
            Term.freeSupport])
    simpa [graph, graphBody, arguments] using hBase
  apply graph_presentation.exists_conj_of_case
  · intro source hSource
    cases hSource
  · exact hExists
  · have hWitnessGraph :
        Derives pairing_operator_theory
          [graphBody] graphBody :=
      Derives.assumption_of_mem (by simp)
    have hPairGraph :
        Derives pairing_operator_theory
          [graphBody]
          (singleton_spec (x#1) pair) := by
      have hPairSpec :=
        unordered_pair_term_spec_derives
          (x#1) (x#1)
          (set_variable_admissible 1)
          (set_variable_admissible 1)
      have hBridge :=
        pair_repeated_spec_iff_singleton_spec
          (x#1) pair
          (set_variable_admissible 1)
          hPair
      exact (Derives.iff_elim_right
        (Derives.of_empty hBridge)
        hPairSpec).context_weaken_cons
    have hFunctional :=
      graph_presentation.functional
        hArguments hZero hPair
    have hFunctional' :
        Derives pairing_operator_theory
          [graphBody]
          (Formula.imp graphBody
            (Formula.imp
              (singleton_spec (x#1) pair)
              ((x#0) ≐ₘ pair))) := by
      simpa [graphBody, arguments, pair, graph] using
        hFunctional.context_weaken_cons
    exact (hFunctional'.imp_elim
      hWitnessGraph).imp_elim hPairGraph

/-- 无序对函数理论中的公理不含单点集函数，故编译后严格保持不变。 -/
private theorem formula_base_eq
    {source : SetFormula}
    (hSource : pairing_operator_theory source) :
    FunctionGraphElimination.formula data source =
      source := by
  apply formula_eq_of_sentence_avoids
    data source
  · change
      source = pair_definition_axiom ∨
        (source = pairing_axiom ∨
          extensionality_theory source) at hSource
    rcases hSource with rfl | hSource
    · simpa [pair_definition_axiom] using
        formula_avoids_forall_close
          FunctionSymbol.singleton
          [(SetSort.set, 0),
            (SetSort.set, 1),
            (SetSort.set, 2)]
          (pair_definition_instance
            (x#0) (x#1) (x#2)) <| by
              simp [pair_definition_instance,
                pair_spec, pair_member_condition,
                unordered_pair_term,
                FormulaAvoids, TermsAvoid,
                TermAvoids]
    · rcases hSource with rfl | hSource
      · simpa [pairing_axiom] using
          formula_avoids_forall_close
            FunctionSymbol.singleton
            [(SetSort.set, 0),
              (SetSort.set, 1)]
            (pair_exists (x#0) (x#1)) <| by
              simp [pair_exists,
                pair_member_condition,
                FormulaAvoids, TermsAvoid,
                TermAvoids]
      · change source = extensionality_axiom
          at hSource
        subst source
        simpa [extensionality_axiom] using
          formula_avoids_forall_close
            FunctionSymbol.singleton
            [(SetSort.set, 0),
              (SetSort.set, 1)]
            (extensionality_instance
              (x#0) (x#1)) <| by
                simp [extensionality_instance,
                  agreement_to_equality,
                  membership_agreement,
                  FormulaAvoids, TermsAvoid,
                  TermAvoids]
  · exact pairing_operator_theory_sentence
      hSource

/-- 已证明的开放单点集编译可沿源变量闭合。 -/
private theorem formula_forall_close_derives
    (id : FreeVarId) (source : SetFormula)
    (hSource : Formula.Admissible source)
    (hCompiled :
      Derives pairing_operator_theory []
        (FunctionGraphElimination.formula
          data source)) :
    Derives pairing_operator_theory []
      (FunctionGraphElimination.formula data
        (Formula.forallE SetSort.set
          (Formula.closeFreeAt
            SetSort.set id 0 source))) := by
  have hClosed :
      Derives pairing_operator_theory []
        (Formula.forallE SetSort.set
          (Formula.closeFreeAt SetSort.set
            (source_id id) 0
            (FunctionGraphElimination.formula
              data source))) := by
    apply Derives.forall_intro
    · exact theory_fresh (source_id id)
    · intro formula hFormula
      cases hFormula
    · exact hCompiled
  exact Derives.iff_elim_left
    (graph_presentation.formula_forall_close_iff
      SetSort.set id source hSource)
    hClosed

private theorem formula_definition_axiom_derives :
    Derives pairing_operator_theory []
      (FunctionGraphElimination.formula
        data singleton_definition_axiom) := by
  have hPoint :
      Derives pairing_operator_theory []
        (FunctionGraphElimination.formula
          data definition_point) := by
    rw [formula_definition_point]
    exact compiled_definition_point_derives
  have hAdmissible :
      Formula.Admissible definition_point :=
    singleton_definition_instance_admissible
      (set_variable_admissible 0)
  have hClosed :=
    formula_forall_close_derives
      0 definition_point hAdmissible hPoint
  simpa [singleton_definition_axiom,
    definition_point] using hClosed

private theorem compile_axiom
    {source : SetFormula}
    (hSource :
      singleton_operator_theory source) :
    Derives pairing_operator_theory []
      (FunctionGraphElimination.formula
        data source) := by
  rcases hSource with rfl | hSource
  · exact formula_definition_axiom_derives
  · rw [formula_base_eq hSource]
    exact Derives.theory_mem hSource
      (hFormulaCheck :=
        Formula.check_certificate_of_admissible
          (pairing_operator_theory_admissible
            source hSource))

/-- 单点集函数扩张的理论级函数图消去表示。 -/
def theory_presentation :
    TheoryPresentation data where
  graph := graph_presentation
  source := singleton_operator_theory
  compile_axiom := compile_axiom

theorem hilbert
    {source : SetFormula}
    (hSource :
      HilbertDerives
        singleton_operator_theory source) :
    Derives pairing_operator_theory []
      (FunctionGraphElimination.formula
        data source) :=
  theory_presentation.hilbert hSource

/-- 单点集函数扩张的 checked 自然演绎证明可整体翻译到无序对函数理论。 -/
theorem derives
    {source : SetFormula}
    (hSource :
      Derives singleton_operator_theory []
        source) :
    Derives pairing_operator_theory []
      (FunctionGraphElimination.formula
        data source) :=
  theory_presentation.derives
    SetSort.set hSource

theorem hilbert_falsum
    (hSource :
      HilbertDerives
        singleton_operator_theory
        Formula.falsum) :
    Derives pairing_operator_theory []
      Formula.falsum :=
  theory_presentation.hilbert_falsum hSource

theorem derives_falsum
    (hSource :
      Derives singleton_operator_theory []
        Formula.falsum) :
    Derives pairing_operator_theory []
      Formula.falsum :=
  theory_presentation.derives_falsum
    SetSort.set hSource

theorem consistent
    (hBase :
      Derives.Consistent
        pairing_operator_theory []) :
    Derives.Consistent
      singleton_operator_theory [] :=
  theory_presentation.consistent
    SetSort.set hBase

theorem hilbert_consistent
    (hBase :
      Derives.Consistent
        pairing_operator_theory []) :
    ¬ HilbertDerives
        singleton_operator_theory
        Formula.falsum :=
  theory_presentation.hilbert_consistent hBase

private theorem realizes
    {arguments : List SetTerm}
    (hArguments :
      ArgsAdmissible arguments
        (signature.funcDomain
          FunctionSymbol.singleton)) :
    Derives singleton_operator_theory [] <|
      graph arguments
        (.app FunctionSymbol.singleton
          arguments) := by
  change ArgsAdmissible arguments [SetSort.set]
    at hArguments
  rcases singleton_admissible hArguments with
    ⟨element, rfl, hElement⟩
  simpa [graph, singleton_term] using
    singleton_term_spec_derives
      element hElement

def presentation : DefinitionPresentation data where
  toGraphPresentation := graph_presentation
  extension := singleton_operator_theory
  extension_sentence :=
    singleton_operator_theory_sentence
  base_subset := by
    intro φ hφ
    exact Or.inr hφ
  realizes := realizes

theorem sentence_iff
    {source : SetFormula}
    (hSource : Formula.Sentence source) :
    Derives singleton_operator_theory []
      (Formula.iff
        (FunctionGraphElimination.formula
          data source)
        source) :=
  presentation.sentence_iff hSource

end Singleton
end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
