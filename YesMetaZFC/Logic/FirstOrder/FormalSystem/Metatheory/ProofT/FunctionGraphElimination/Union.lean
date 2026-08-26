import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Hilbert
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Union

/-!
# 一元并函数图消去实例

一元并函数使用 `union_spec` 作为图公式。图的全体性来自并集存在公理，单值性来自
外延性；定义公理的编译在逐元素层面重放这两个合同。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace FunctionGraphElimination
namespace Union

open Nonlogical.BasicSetTheory
open scoped Symbols

set_option autoImplicit false

/-- 一元并图；错误元数仅作为不可达的良构性外分支落到假。 -/
def graph : List SetTerm → SetTerm → SetFormula
  | (source :: []), result =>
      union_spec source result
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

private theorem push_push_scoped
    {scope : Scope signature} {term : SetTerm}
    (hTerm : TermScoped scope term) :
    TermScoped
      (Scope.push (Scope.push scope SetSort.set)
        SetSort.set) term :=
  push_scoped (push_scoped hTerm)

private theorem graph_well_formed
    {arguments : List SetTerm} {result : SetTerm}
    (hArguments :
      ArgsWellSorted arguments
        (signature.funcDomain FunctionSymbol.union))
    (hResult :
      TermWellSorted result SetSort.set) :
    FormulaWellFormed (graph arguments result) := by
  change ArgsWellSorted arguments [SetSort.set]
    at hArguments
  cases hArguments with
  | cons hSource hTail =>
      cases hTail
      unfold graph union_spec
      apply FormulaWellFormed.forallE
      apply FormulaWellFormed.iff
      · apply FormulaWellFormed.rel
        simpa [signature] using
          ArgsWellSorted.cons
            (TermWellSorted.bvar
              (σ := signature) SetSort.set 0)
            (ArgsWellSorted.cons hResult
              ArgsWellSorted.nil)
      · apply FormulaWellFormed.existsE
        apply FormulaWellFormed.conj
        · apply FormulaWellFormed.rel
          simpa [signature] using
            ArgsWellSorted.cons
              (TermWellSorted.bvar
                (σ := signature) SetSort.set 0)
              (ArgsWellSorted.cons hSource
                ArgsWellSorted.nil)
        · apply FormulaWellFormed.rel
          simpa [signature] using
            ArgsWellSorted.cons
              (TermWellSorted.bvar
                (σ := signature) SetSort.set 1)
              (ArgsWellSorted.cons
                (TermWellSorted.bvar
                  (σ := signature) SetSort.set 0)
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
      exact FormulaScoped.falsum
  | cons source tail =>
      cases tail with
      | nil =>
          unfold graph union_spec
          apply FormulaScoped.forallE
          apply FormulaScoped.iff
          · apply FormulaScoped.rel
            intro term hTerm
            rcases List.mem_cons.mp hTerm with rfl | hTerm
            · exact TermScoped.bvar <| by
                simp [Scope.push]
            · rw [List.mem_singleton.mp hTerm]
              exact push_scoped hResult
          · apply FormulaScoped.existsE
            apply FormulaScoped.conj
            · apply FormulaScoped.rel
              intro term hTerm
              rcases List.mem_cons.mp hTerm with rfl | hTerm
              · exact TermScoped.bvar <| by
                  simp [Scope.push]
              · rw [List.mem_singleton.mp hTerm]
                exact push_push_scoped <|
                  hArguments source (by simp)
            · apply FormulaScoped.rel
              intro term hTerm
              rcases List.mem_cons.mp hTerm with rfl | hTerm
              · exact TermScoped.bvar <| by
                  simp [Scope.push]
              · rw [List.mem_singleton.mp hTerm]
                exact TermScoped.bvar <| by
                  simp [Scope.push]
      | cons second rest =>
          exact FormulaScoped.falsum

private theorem graph_freeSupport
    {arguments : List SetTerm} {result : SetTerm}
    {freeVariable : FreeVariable signature}
    (hMember :
      freeVariable ∈
        Formula.freeSupport (graph arguments result)) :
    freeVariable ∈ Term.freeSupportList arguments ∨
      freeVariable ∈ Term.freeSupport result := by
  cases arguments with
  | nil =>
      simp [graph, Formula.freeSupport] at hMember
  | cons source tail =>
      cases tail with
      | nil =>
          simpa [graph, union_spec,
            Formula.freeSupport,
            Term.freeSupportList,
            Term.freeSupport, or_comm,
            or_left_comm, or_assoc] using hMember
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
          simp [graph, union_spec,
            Formula.substituteFree,
            Term.substituteFree]
      | cons second rest =>
          rfl

private theorem graph_avoids
    {arguments : List SetTerm} {result : SetTerm}
    (hArguments :
      TermsAvoid FunctionSymbol.union arguments)
    (hResult :
      TermAvoids FunctionSymbol.union result) :
    FormulaAvoids FunctionSymbol.union
      (graph arguments result) := by
  cases arguments with
  | nil =>
      trivial
  | cons source tail =>
      cases tail with
      | nil =>
          have hSource := hArguments source (by simp)
          simp [graph, union_spec,
            FormulaAvoids, TermsAvoid, TermAvoids,
            hSource, hResult]
      | cons second rest =>
          trivial

/-- 已实现的一元并函数图消去数据。 -/
def data : Data signature where
  symbol := FunctionSymbol.union
  sort := SetSort.set
  codomain_eq := rfl
  graph := Union.graph
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
        (signature.funcDomain FunctionSymbol.union))
    (hFresh :
      (SetSort.set, resultId) ∉
        Term.freeSupportList arguments) :
    Derives union_theory [] <|
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
  have hSourceClose₁ :
      Term.closeFreeAt SetSort.set resultId 1 source =
        source :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set resultId 1 source hSource.2 hSourceFresh
  have hSourceClose₂ :
      Term.closeFreeAt SetSort.set resultId 2 source =
        source :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set resultId 2 source hSource.2 hSourceFresh
  simpa [graph, union_exists, union_spec,
    Formula.closeFreeAt, Formula.next_depth,
    Term.closeFreeAt, hSourceClose₁,
    hSourceClose₂] using
    union_exists_derives source hSource

private theorem functional
    {arguments : List SetTerm}
    {left right : SetTerm}
    (hArguments :
      ArgsAdmissible arguments
        (signature.funcDomain FunctionSymbol.union))
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    Derives union_theory [] <|
      Formula.imp (graph arguments left) <|
        Formula.imp (graph arguments right) <|
          Formula.equal left right := by
  change ArgsAdmissible arguments [SetSort.set]
    at hArguments
  rcases singleton_admissible hArguments with
    ⟨source, rfl, hSource⟩
  apply Derives.theory_weaken
    (T := extensionality_theory)
  · intro φ hφ
    exact Or.inr hφ
  · simpa [graph] using
      union_unique source left right
        hSource hLeft hRight

/-- 并集存在理论给出的全体、单值一元并图表示。 -/
def graph_presentation : GraphPresentation data where
  theory := union_theory
  theory_sentence := by
    intro φ hφ
    exact union_operator_theory_sentence
      (Or.inr hφ)
  total := total
  functional := functional

/-- 打开一元并规格量词后右侧的成员见证公式。 -/
private def descriptor_point : SetFormula :=
  ∃ₘ[SetSort.set],
    (bₛ#0 ∈ₘ x#0) ∧ₘ
      (x#1 ∈ₘ bₛ#0)

/-- 右侧成员见证公式只执行奇数区变量重编码。 -/
private def compiled_descriptor_point : SetFormula :=
  ∃ₘ[SetSort.set],
    (bₛ#0 ∈ₘ x#1) ∧ₘ
      (x#3 ∈ₘ bₛ#0)

/-- 打开一元并规格量词后的源层逐元素公式。 -/
private def definition_point : SetFormula :=
  (x#1 ∈ₘ ⋃ₘ (x#0)) ↔ₘ descriptor_point

/-- 逐元素公式消去一元并函数项后的显式图正规形。 -/
private def compiled_definition_point : SetFormula :=
  ((∃ₘ[SetSort.set, 0],
      union_spec (x#1) (x#0) ∧ₘ
        (x#3 ∈ₘ x#0)) ↔ₘ
    compiled_descriptor_point)

/-- 不含一元并函数的成员见证公式只执行奇数区变量重编码。 -/
private theorem formula_descriptor_point :
    FunctionGraphElimination.formula data descriptor_point =
      compiled_descriptor_point := by
  rw [formula_eq_source_of_avoids]
  · simp [descriptor_point, compiled_descriptor_point,
      source_formula, source_term, source_id]
  · simp [descriptor_point, FormulaAvoids,
      TermsAvoid, TermAvoids, data]

/-- 逐元素公式的编译只生成一个一元并图见证。 -/
private theorem formula_definition_point :
    FunctionGraphElimination.formula
        data definition_point =
      compiled_definition_point := by
  unfold definition_point
  rw [FunctionGraphElimination.formula]
  rw [formula_descriptor_point]
  simp [
    compiled_definition_point,
    FunctionGraphElimination.formula,
    FunctionGraphElimination.relation,
    FunctionGraphElimination.terms,
    FunctionGraphElimination.term,
    close_witnesses, condition_conjunction,
    data, graph, source_id, witness_id]

/-- 并集存在理论中的任意公理不含一元并函数，故编译后严格保持不变。 -/
private theorem formula_base_eq
    {source : SetFormula}
    (hSource : union_theory source) :
    FunctionGraphElimination.formula data source =
      source := by
  apply formula_eq_of_sentence_avoids data source
  · rcases hSource with rfl | hSource
    · simpa [union_axiom] using
        formula_avoids_forall_close
          FunctionSymbol.union
          [(SetSort.set, 0)]
          (union_exists (x#0)) <| by
            simp [union_exists,
              FormulaAvoids, TermsAvoid, TermAvoids]
    · change source = extensionality_axiom at hSource
      subst source
      simpa [extensionality_axiom] using
        formula_avoids_forall_close
          FunctionSymbol.union
          [(SetSort.set, 0), (SetSort.set, 1)]
          (extensionality_instance
            (x#0) (x#1)) <| by
              simp [extensionality_instance,
                agreement_to_equality,
                membership_agreement,
                FormulaAvoids, TermsAvoid, TermAvoids]
  · exact graph_presentation.theory_sentence hSource

/-- 并集存在理论是闭句理论，因而任意证明级 eigenvariable 均对理论新鲜。 -/
private theorem theory_fresh
    (id : FreeVarId) :
    ∀ source, union_theory source →
      (SetSort.set, id) ∉
        Formula.freeSupport source := by
  intro source hSource
  rw [(graph_presentation.theory_sentence hSource).2]
  exact List.not_mem_nil

/-- 并集规格逐点证明编译后的定义公式。 -/
private theorem compiled_definition_point_derives :
    Derives union_theory []
      compiled_definition_point := by
  unfold compiled_definition_point
  let descriptor : SetFormula :=
    ∃ₘ[SetSort.set],
      (bₛ#0 ∈ₘ x#1) ∧ₘ
        (x#3 ∈ₘ bₛ#0)
  apply Derives.iff_intro
  ·
    let body :=
      Formula.conj
        (union_spec (x#1) (x#0))
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
        (Derives.assumption_of_mem (by simp) :
          Derives union_theory
            [∃ₘ[SetSort.set, 0], body]
            (∃ₘ[SetSort.set, 0], body))
    · have hBody :
          Derives union_theory
            [body, ∃ₘ[SetSort.set, 0], body]
            body :=
        Derives.assumption_of_mem (by simp)
      have hSpec :=
        Derives.conj_elim_left hBody
      have hMember :=
        Derives.conj_elim_right hBody
      have hAtRaw :=
        Derives.forall_elim
          (term := x#3) hSpec
      have hAt :
          Derives union_theory
            [body, ∃ₘ[SetSort.set, 0], body]
            ((x#3 ∈ₘ x#0) ↔ₘ descriptor) := by
        simpa [body, descriptor, union_spec,
          Formula.openAt, Term.openAt,
          set_variable] using hAtRaw
      exact Derives.iff_elim_right hAt hMember
  ·
    let graphBody := union_spec (x#1) (x#0)
    have hArguments :
        ArgsAdmissible [x#1] [SetSort.set] :=
      ArgsAdmissible.cons
        (set_variable_admissible 1)
        ArgsAdmissible.nil
    have hExists :
        Derives union_theory [descriptor]
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
          Derives union_theory
            [graphBody, descriptor] graphBody :=
        Derives.assumption_of_mem (by simp)
      have hDescriptor :
          Derives union_theory
            [graphBody, descriptor] descriptor :=
        Derives.assumption_of_mem (by simp)
      have hAtRaw :=
        Derives.forall_elim
          (term := x#3) hSpec
      have hAt :
          Derives union_theory
            [graphBody, descriptor]
            ((x#3 ∈ₘ x#0) ↔ₘ descriptor) := by
        simpa [graphBody, descriptor, union_spec,
          Formula.openAt, Term.openAt,
          set_variable] using hAtRaw
      exact Derives.iff_elim_left hAt hDescriptor

/-- 并集存在理论证明开放定义实例的函数图编译。 -/
private theorem formula_definition_instance_derives :
    Derives union_theory []
      (FunctionGraphElimination.formula data
        (union_definition_instance (x#0))) := by
  have hPoint :
      Derives union_theory []
        (FunctionGraphElimination.formula
          data definition_point) := by
    rw [formula_definition_point]
    exact compiled_definition_point_derives
  have hElement :
      Derives union_theory []
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
    (bₛ#0 ∈ₘ ⋃ₘ (x#0)) ↔ₘ
      (∃ₘ[SetSort.set],
        (bₛ#0 ∈ₘ x#0) ∧ₘ
          (bₛ#1 ∈ₘ bₛ#0))
  have hForall :
      Formula.Admissible
        (Formula.forallE SetSort.set body) := by
    simpa [body, union_definition_instance,
      union_spec] using
      union_definition_instance_admissible
        (set_variable_admissible 0)
  have hNormalized :=
    graph_presentation.formula_forall_iff_at
      SetSort.set body hForall 1 (by native_decide)
  apply Derives.iff_elim_left hNormalized
  simpa [body, definition_point,
    Formula.openAt, Term.openAt,
    set_variable] using hElement

/-- 并集存在理论证明整个一元并定义公理的函数图编译。 -/
private theorem formula_definition_axiom_derives :
    Derives union_theory []
      (FunctionGraphElimination.formula
        data union_definition_axiom) := by
  have hInstance :
      Formula.Admissible
        (union_definition_instance (x#0)) :=
    union_definition_instance_admissible
      (set_variable_admissible 0)
  have hClosed :=
    graph_presentation.formula_forall_close_derives
      SetSort.set 0
      (union_definition_instance (x#0))
      hInstance formula_definition_instance_derives
  simpa [union_definition_axiom] using hClosed

private theorem compile_axiom
    {source : SetFormula}
    (hSource : union_operator_theory source) :
    Derives union_theory []
      (FunctionGraphElimination.formula data source) := by
  rcases hSource with rfl | hSource
  · exact formula_definition_axiom_derives
  · rw [formula_base_eq hSource]
    exact Derives.theory_mem hSource
      (hFormulaCheck :=
        Formula.check_certificate_of_admissible
          (union_theory_admissible source hSource))

/-- 一元并函数扩张的理论级函数图消去表示。 -/
def theory_presentation : TheoryPresentation data where
  graph := graph_presentation
  source := union_operator_theory
  compile_axiom := compile_axiom

theorem hilbert
    {source : SetFormula}
    (hSource :
      HilbertDerives union_operator_theory source) :
    Derives union_theory []
      (FunctionGraphElimination.formula data source) :=
  theory_presentation.hilbert hSource

/-- 一元并扩张的 checked 自然演绎证明可整体翻译到并集存在理论。 -/
theorem derives
    {source : SetFormula}
    (hSource :
      Derives union_operator_theory [] source) :
    Derives union_theory []
      (FunctionGraphElimination.formula data source) :=
  theory_presentation.derives SetSort.set hSource

theorem hilbert_falsum
    (hSource :
      HilbertDerives union_operator_theory
        Formula.falsum) :
    Derives union_theory [] Formula.falsum :=
  theory_presentation.hilbert_falsum hSource

theorem derives_falsum
    (hSource :
      Derives union_operator_theory []
        Formula.falsum) :
    Derives union_theory [] Formula.falsum :=
  theory_presentation.derives_falsum
    SetSort.set hSource

theorem consistent
    (hBase : Derives.Consistent union_theory []) :
    Derives.Consistent union_operator_theory [] :=
  theory_presentation.consistent SetSort.set hBase

theorem hilbert_consistent
    (hBase : Derives.Consistent union_theory []) :
    ¬ HilbertDerives union_operator_theory
        Formula.falsum :=
  theory_presentation.hilbert_consistent hBase

private theorem realizes
    {arguments : List SetTerm}
    (hArguments :
      ArgsAdmissible arguments
        (signature.funcDomain FunctionSymbol.union)) :
    Derives union_operator_theory [] <|
      graph arguments
        (.app FunctionSymbol.union arguments) := by
  change ArgsAdmissible arguments [SetSort.set]
    at hArguments
  rcases singleton_admissible hArguments with
    ⟨source, rfl, hSource⟩
  simpa [graph, union_term] using
    union_term_spec_derives source hSource

/-- 一元并函数定义扩张的完整函数图表示。 -/
def presentation : DefinitionPresentation data where
  toGraphPresentation := graph_presentation
  extension := union_operator_theory
  extension_sentence := union_operator_theory_sentence
  base_subset := by
    intro φ hφ
    exact Or.inr hφ
  realizes := realizes

theorem sentence_iff
    {source : SetFormula}
    (hSource : Formula.Sentence source) :
    Derives union_operator_theory []
      (Formula.iff
        (FunctionGraphElimination.formula data source)
        source) :=
  presentation.sentence_iff hSource

end Union
end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
