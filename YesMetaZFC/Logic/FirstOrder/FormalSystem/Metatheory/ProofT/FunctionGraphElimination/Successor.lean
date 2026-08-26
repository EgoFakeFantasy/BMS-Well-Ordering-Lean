import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Canonical
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Successor

/-!
# 后继函数图消去实例

后继函数以既有二元并与无序对复合项 `x ∪ {x,x}` 为规范图。定义公理本身就是
函数项与该规范项的等式，因此开放公理的编译只产生一个图见证。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace FunctionGraphElimination
namespace Successor

open Nonlogical.BasicSetTheory
open scoped Symbols

set_option autoImplicit false

private theorem witness_well_sorted
    {source : SetTerm}
    (hSource : TermWellSorted source SetSort.set) :
    TermWellSorted (successor_witness_term source)
      SetSort.set := by
  have hPair :
      TermWellSorted (unordered_pair_term source source)
        SetSort.set := by
    simpa [unordered_pair_term, signature] using
      (TermWellSorted.app
        (σ := signature) FunctionSymbol.unorderedPair
        (ArgsWellSorted.cons hSource
          (ArgsWellSorted.cons hSource ArgsWellSorted.nil)))
  simpa [successor_witness_term, binary_union_term,
      signature] using
    (TermWellSorted.app
      (σ := signature) FunctionSymbol.binaryUnion
      (ArgsWellSorted.cons hSource
        (ArgsWellSorted.cons hPair ArgsWellSorted.nil)))

private theorem witness_scoped
    {scope : Scope signature} {source : SetTerm}
    (hSource : TermScoped scope source) :
    TermScoped scope (successor_witness_term source) := by
  have hPair :
      TermScoped scope
        (unordered_pair_term source source) := by
    simpa [unordered_pair_term] using
      (TermScoped.app
        (σ := signature) (ctx := scope)
        FunctionSymbol.unorderedPair [source, source] (by
          intro term hTerm
          rcases List.mem_cons.mp hTerm with rfl | hTerm
          · exact hSource
          · rw [List.mem_singleton.mp hTerm]
            exact hSource))
  simpa [successor_witness_term, binary_union_term] using
    (TermScoped.app
      (σ := signature) (ctx := scope)
      FunctionSymbol.binaryUnion
      [source, unordered_pair_term source source] (by
        intro term hTerm
        rcases List.mem_cons.mp hTerm with rfl | hTerm
        · exact hSource
        · rw [List.mem_singleton.mp hTerm]
          exact hPair))

private theorem witness_freeSupport
    {source : SetTerm}
    {freeVariable : FreeVariable signature}
    (hMember :
      freeVariable ∈
        Term.freeSupport (successor_witness_term source)) :
    freeVariable ∈ Term.freeSupport source := by
  simpa [successor_witness_term, binary_union_term,
    unordered_pair_term, Term.freeSupport,
    Term.freeSupportList] using hMember

private theorem witness_substituteFree
    (target : SetSort) (id : FreeVarId)
    (replacement source : SetTerm) :
    successor_witness_term
        (Term.substituteFree target id replacement source) =
      Term.substituteFree target id replacement
        (successor_witness_term source) := by
  cases target
  simp [successor_witness_term, binary_union_term,
    unordered_pair_term, Term.substituteFree]

private theorem witness_avoids
    {source : SetTerm}
    (hSource : TermAvoids FunctionSymbol.successor source) :
    TermAvoids FunctionSymbol.successor
      (successor_witness_term source) := by
  simp [successor_witness_term, binary_union_term,
    unordered_pair_term, TermAvoids, hSource]

/-- 后继函数由规范项 `x ∪ {x,x}` 给出的 unary graph 数据。 -/
def canonical_data :
    CanonicalGraph.Unary signature where
  symbol := FunctionSymbol.successor
  sourceSort := SetSort.set
  resultSort := SetSort.set
  domain_eq := rfl
  codomain_eq := rfl
  canonical := successor_witness_term
  canonical_well_formed := witness_well_sorted
  canonical_scoped := witness_scoped
  canonical_freeSupport := witness_freeSupport
  canonical_substituteFree := witness_substituteFree
  canonical_avoids := witness_avoids

/-- 一元后继函数图；错误元数在良构分支外落到假。 -/
def graph : List SetTerm → SetTerm → SetFormula :=
  canonical_data.graph

/-- 已实现的后继函数图消去数据。 -/
def data : Data signature :=
  canonical_data.data

private theorem source_admissible
    {arguments : List SetTerm}
    (hArguments :
      ArgsAdmissible arguments [SetSort.set]) :
    ∃ source,
      arguments = [source] ∧
        Term.Admissible source SetSort.set := by
  simpa [canonical_data] using
    canonical_data.argument_admissible hArguments

/-- 二元并描述符理论给出的全体、单值后继规范图。 -/
def graph_presentation : GraphPresentation data :=
  canonical_data.graph_presentation
    successor_base_theory
    successor_base_theory_sentence

/-- 外层 binder 打开后的后继定义实例。 -/
private def definition_point : SetFormula :=
  successor_definition_instance (x#0)

/-- 开放后继定义实例的显式图正规形。 -/
private def compiled_definition_point : SetFormula :=
  ∃ₘ[SetSort.set, 0],
    graph [x#1] (x#0) ∧ₘ
      ((x#0) ≐ₘ successor_witness_term (x#1))

/-- 开放定义实例的编译只生成一个规范后继见证。 -/
private theorem formula_definition_point :
    FunctionGraphElimination.formula data definition_point =
      compiled_definition_point := by
  unfold definition_point successor_definition_instance
  rw [FunctionGraphElimination.formula]
  simp [compiled_definition_point,
    FunctionGraphElimination.equality,
    FunctionGraphElimination.terms,
    FunctionGraphElimination.term,
    close_witnesses, condition_conjunction,
    data, graph, canonical_data,
    CanonicalGraph.Unary.data,
    CanonicalGraph.Unary.graph,
    successor_witness_term, binary_union_term,
    unordered_pair_term, source_id, witness_id]

/-- 二元并描述符理论逐点证明编译后的后继定义公式。 -/
private theorem compiled_definition_point_derives :
    Derives successor_base_theory []
      compiled_definition_point := by
  unfold compiled_definition_point
  let witness := successor_witness_term (x#1)
  have hWitness :
      Term.Admissible witness SetSort.set := by
    simpa [witness] using
      successor_witness_term_admissible
        (x#1) (set_variable_admissible 1)
  nd_apply Derives.exists_intro (term := witness)
  simpa [witness, graph, canonical_data,
      CanonicalGraph.Unary.graph,
      successor_witness_term, binary_union_term,
      unordered_pair_term,
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.substituteFree, Term.substituteFree] using
    Derives.conj_intro
      (Derives.eq_refl_m
        (T := successor_base_theory) (Γ := [])
        witness (sort := SetSort.set)
        (hTermCheck :=
          Term.check_certificate_of_admissible hWitness))
      (Derives.eq_refl_m
        (T := successor_base_theory) (Γ := [])
        witness (sort := SetSort.set)
        (hTermCheck :=
          Term.check_certificate_of_admissible hWitness))

/--
二元并描述符理论的固定公理都不含后继函数，因此编译后保持原闭句不变。
-/
private theorem formula_base_eq
    {source : SetFormula}
    (hSource : successor_base_theory source) :
    FunctionGraphElimination.formula data source = source := by
  apply formula_eq_of_sentence_avoids data source
  · change binary_union_operator_theory source at hSource
    rcases hSource with rfl | hSource
    · simpa [data, canonical_data,
          CanonicalGraph.Unary.data,
          binary_union_definition_axiom] using
        formula_avoids_forall_close
          FunctionSymbol.successor
          [(SetSort.set, 0), (SetSort.set, 1)]
          (binary_union_definition_instance
            (x#0) (x#1)) <| by
              simp [binary_union_definition_instance,
                binary_union_term, union_term,
                unordered_pair_term,
                FormulaAvoids, TermAvoids]
    · rcases hSource with hSource | hSource
      · rcases hSource with rfl | hSource
        · simpa [data, canonical_data,
              CanonicalGraph.Unary.data,
              pair_definition_axiom] using
            formula_avoids_forall_close
              FunctionSymbol.successor
              [(SetSort.set, 0), (SetSort.set, 1),
                (SetSort.set, 2)]
              (pair_definition_instance
                (x#0) (x#1) (x#2)) <| by
                  simp [pair_definition_instance,
                    pair_spec, pair_member_condition,
                    unordered_pair_term,
                    FormulaAvoids, TermsAvoid, TermAvoids]
        · rcases hSource with rfl | hSource
          · simpa [data, canonical_data,
                CanonicalGraph.Unary.data,
                pairing_axiom] using
              formula_avoids_forall_close
                FunctionSymbol.successor
                [(SetSort.set, 0), (SetSort.set, 1)]
                (pair_exists (x#0) (x#1)) <| by
                  simp [pair_exists,
                    pair_member_condition,
                    FormulaAvoids, TermsAvoid, TermAvoids]
          · change source = extensionality_axiom at hSource
            subst source
            simpa [data, canonical_data,
                CanonicalGraph.Unary.data,
                extensionality_axiom] using
              formula_avoids_forall_close
                FunctionSymbol.successor
                [(SetSort.set, 0), (SetSort.set, 1)]
                (extensionality_instance
                  (x#0) (x#1)) <| by
                    simp [extensionality_instance,
                      agreement_to_equality,
                      membership_agreement,
                      FormulaAvoids, TermsAvoid, TermAvoids]
      · rcases hSource with rfl | hSource
        · simpa [data, canonical_data,
              CanonicalGraph.Unary.data,
              union_definition_axiom] using
            formula_avoids_forall_close
              FunctionSymbol.successor
              [(SetSort.set, 0)]
              (union_definition_instance (x#0)) <| by
                simp [union_definition_instance,
                  union_spec, union_term,
                  FormulaAvoids, TermsAvoid, TermAvoids]
        · rcases hSource with rfl | hSource
          · simpa [data, canonical_data,
                CanonicalGraph.Unary.data,
                union_axiom] using
              formula_avoids_forall_close
                FunctionSymbol.successor
                [(SetSort.set, 0)]
                (union_exists (x#0)) <| by
                  simp [union_exists,
                    FormulaAvoids, TermsAvoid, TermAvoids]
          · change source = extensionality_axiom at hSource
            subst source
            simpa [data, canonical_data,
                CanonicalGraph.Unary.data,
                extensionality_axiom] using
              formula_avoids_forall_close
                FunctionSymbol.successor
                [(SetSort.set, 0), (SetSort.set, 1)]
                (extensionality_instance
                  (x#0) (x#1)) <| by
                    simp [extensionality_instance,
                      agreement_to_equality,
                      membership_agreement,
                      FormulaAvoids, TermsAvoid, TermAvoids]
  · exact successor_base_theory_sentence hSource

/-- 二元并描述符理论证明完整后继定义公理的函数图编译。 -/
private theorem formula_definition_axiom_derives :
    Derives successor_base_theory []
      (FunctionGraphElimination.formula
        data successor_definition_axiom) := by
  have hPoint :
      Derives successor_base_theory []
        (FunctionGraphElimination.formula
          data definition_point) := by
    rw [formula_definition_point]
    exact compiled_definition_point_derives
  have hPointAdmissible :
      Formula.Admissible definition_point :=
    successor_definition_instance_admissible
      (set_variable_admissible 0)
  have hClosed :=
    graph_presentation.formula_forall_close_derives
      SetSort.set 0 definition_point
      hPointAdmissible hPoint
  simpa [successor_definition_axiom,
    definition_point] using hClosed

private theorem compile_axiom
    {source : SetFormula}
    (hSource : successor_operator_theory source) :
    Derives successor_base_theory []
      (FunctionGraphElimination.formula data source) := by
  rcases hSource with rfl | hSource
  · exact formula_definition_axiom_derives
  · rw [formula_base_eq hSource]
    exact Derives.theory_mem hSource
      (hFormulaCheck :=
        Formula.check_certificate_of_admissible
          (successor_base_theory_admissible
            source hSource))

/-- 后继函数扩张的理论级函数图消去表示。 -/
def theory_presentation : TheoryPresentation data where
  graph := graph_presentation
  source := successor_operator_theory
  compile_axiom := compile_axiom

theorem hilbert
    {source : SetFormula}
    (hSource :
      HilbertDerives successor_operator_theory source) :
    Derives successor_base_theory []
      (FunctionGraphElimination.formula data source) :=
  theory_presentation.hilbert hSource

/-- 后继扩张的 checked 自然演绎证明可整体翻译到二元并理论。 -/
theorem derives
    {source : SetFormula}
    (hSource :
      Derives successor_operator_theory [] source) :
    Derives successor_base_theory []
      (FunctionGraphElimination.formula data source) :=
  theory_presentation.derives SetSort.set hSource

theorem hilbert_falsum
    (hSource :
      HilbertDerives successor_operator_theory
        Formula.falsum) :
    Derives successor_base_theory []
      Formula.falsum :=
  theory_presentation.hilbert_falsum hSource

theorem derives_falsum
    (hSource :
      Derives successor_operator_theory []
        Formula.falsum) :
    Derives successor_base_theory []
      Formula.falsum :=
  theory_presentation.derives_falsum
    SetSort.set hSource

theorem consistent
    (hBase :
      Derives.Consistent successor_base_theory []) :
    Derives.Consistent successor_operator_theory [] :=
  theory_presentation.consistent SetSort.set hBase

theorem hilbert_consistent
    (hBase :
      Derives.Consistent successor_base_theory []) :
    ¬ HilbertDerives successor_operator_theory
        Formula.falsum :=
  theory_presentation.hilbert_consistent hBase

private theorem realizes
    {arguments : List SetTerm}
    (hArguments :
      ArgsAdmissible arguments
        (signature.funcDomain FunctionSymbol.successor)) :
    Derives successor_operator_theory [] <|
      graph arguments
        (.app FunctionSymbol.successor arguments) := by
  change ArgsAdmissible arguments [SetSort.set]
    at hArguments
  rcases source_admissible hArguments with
    ⟨source, rfl, hSource⟩
  simpa [graph, canonical_data,
      CanonicalGraph.Unary.graph, successor_term] using
    successor_term_eq_witness_derives source hSource

/-- 后继函数定义扩张的完整函数图表示。 -/
def presentation : DefinitionPresentation data where
  toGraphPresentation := graph_presentation
  extension := successor_operator_theory
  extension_sentence := successor_operator_theory_sentence
  base_subset := by
    intro φ hφ
    exact Or.inr hφ
  realizes := realizes

theorem sentence_iff
    {source : SetFormula}
    (hSource : Formula.Sentence source) :
    Derives successor_operator_theory []
      (Formula.iff
        (FunctionGraphElimination.formula data source)
        source) :=
  presentation.sentence_iff hSource

end Successor
end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
