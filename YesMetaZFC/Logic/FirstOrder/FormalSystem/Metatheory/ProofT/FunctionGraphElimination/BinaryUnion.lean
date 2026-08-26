import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Canonical
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Union

/-!
# 二元并函数图消去实例

二元并函数以既有一元并与无序对复合项 `⋃{a,b}` 为规范图。开放定义公理是函数项
与该规范项的直接等式，因此其编译只产生一个图见证。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace FunctionGraphElimination
namespace BinaryUnion

open Nonlogical.BasicSetTheory
open scoped Symbols

set_option autoImplicit false

/-- 二元并定义右侧的下层规范项。 -/
def witness_term (left right : SetTerm) : SetTerm :=
  union_term (unordered_pair_term left right)

private theorem witness_well_sorted
    {left right : SetTerm}
    (hLeft : TermWellSorted left SetSort.set)
    (hRight : TermWellSorted right SetSort.set) :
    TermWellSorted (witness_term left right)
      SetSort.set := by
  have hPair :
      TermWellSorted (unordered_pair_term left right)
        SetSort.set := by
    simpa [unordered_pair_term, signature] using
      (TermWellSorted.app
        (σ := signature) FunctionSymbol.unorderedPair
        (ArgsWellSorted.cons hLeft
          (ArgsWellSorted.cons hRight ArgsWellSorted.nil)))
  simpa [witness_term, union_term, signature] using
    (TermWellSorted.app
      (σ := signature) FunctionSymbol.union
      (ArgsWellSorted.cons hPair ArgsWellSorted.nil))

private theorem witness_scoped
    {scope : Scope signature} {left right : SetTerm}
    (hLeft : TermScoped scope left)
    (hRight : TermScoped scope right) :
    TermScoped scope (witness_term left right) := by
  have hPair :
      TermScoped scope
        (unordered_pair_term left right) := by
    simpa [unordered_pair_term] using
      (TermScoped.app
        (σ := signature) (ctx := scope)
        FunctionSymbol.unorderedPair [left, right] (by
          intro term hTerm
          rcases List.mem_cons.mp hTerm with rfl | hTerm
          · exact hLeft
          · rw [List.mem_singleton.mp hTerm]
            exact hRight))
  simpa [witness_term, union_term] using
    (TermScoped.app
      (σ := signature) (ctx := scope)
      FunctionSymbol.union
      [unordered_pair_term left right] (by
        intro term hTerm
        rw [List.mem_singleton.mp hTerm]
        exact hPair))

private theorem witness_freeSupport
    {left right : SetTerm}
    {freeVariable : FreeVariable signature}
    (hMember :
      freeVariable ∈
        Term.freeSupport (witness_term left right)) :
    freeVariable ∈ Term.freeSupport left ∨
      freeVariable ∈ Term.freeSupport right := by
  simpa [witness_term, union_term,
    unordered_pair_term, Term.freeSupport,
    Term.freeSupportList] using hMember

private theorem witness_substituteFree
    (target : SetSort) (id : FreeVarId)
    (replacement left right : SetTerm) :
    witness_term
        (Term.substituteFree target id replacement left)
        (Term.substituteFree target id replacement right) =
      Term.substituteFree target id replacement
        (witness_term left right) := by
  cases target
  simp [witness_term, union_term,
    unordered_pair_term, Term.substituteFree]

private theorem witness_avoids
    {left right : SetTerm}
    (hLeft : TermAvoids FunctionSymbol.binaryUnion left)
    (hRight : TermAvoids FunctionSymbol.binaryUnion right) :
    TermAvoids FunctionSymbol.binaryUnion
      (witness_term left right) := by
  simp [witness_term, union_term,
    unordered_pair_term, TermAvoids, hLeft, hRight]

/-- 二元并函数由下层项 `⋃{a,b}` 给出的 canonical graph 数据。 -/
def canonical_data :
    CanonicalGraph.Binary signature where
  symbol := FunctionSymbol.binaryUnion
  leftSort := SetSort.set
  rightSort := SetSort.set
  resultSort := SetSort.set
  domain_eq := rfl
  codomain_eq := rfl
  canonical := witness_term
  canonical_well_formed := witness_well_sorted
  canonical_scoped := witness_scoped
  canonical_freeSupport := witness_freeSupport
  canonical_substituteFree := witness_substituteFree
  canonical_avoids := witness_avoids

/-- 二元并函数图；错误元数在良构分支外落到假。 -/
def graph : List SetTerm → SetTerm → SetFormula :=
  canonical_data.graph

/-- 已实现的二元并函数图消去数据。 -/
def data : Data signature :=
  canonical_data.data

private theorem pair_admissible
    {arguments : List SetTerm}
    (hArguments :
      ArgsAdmissible arguments
        [SetSort.set, SetSort.set]) :
    ∃ left right,
      arguments = [left, right] ∧
        Term.Admissible left SetSort.set ∧
        Term.Admissible right SetSort.set := by
  simpa [canonical_data] using
    canonical_data.arguments_admissible hArguments

/-- 配对与一元并描述符理论给出的全体、单值二元并规范图。 -/
def graph_presentation : GraphPresentation data :=
  canonical_data.graph_presentation
    binary_union_base_theory
    (by
      intro φ hφ
      rcases hφ with hφ | hφ
      · exact pairing_operator_theory_sentence hφ
      · exact union_operator_theory_sentence hφ)

/-- 两个外层 binder 打开后的二元并定义实例。 -/
private def definition_point : SetFormula :=
  binary_union_definition_instance (x#0) (x#1)

/-- 开放二元并定义实例的显式图正规形。 -/
private def compiled_definition_point : SetFormula :=
  ∃ₘ[SetSort.set, 0],
    graph [x#1, x#3] (x#0) ∧ₘ
      ((x#0) ≐ₘ witness_term (x#1) (x#3))

/-- 开放定义实例的编译只生成一个规范二元并见证。 -/
private theorem formula_definition_point :
    FunctionGraphElimination.formula data definition_point =
      compiled_definition_point := by
  unfold definition_point
    binary_union_definition_instance
  rw [FunctionGraphElimination.formula]
  simp [compiled_definition_point,
    FunctionGraphElimination.equality,
    FunctionGraphElimination.terms,
    FunctionGraphElimination.term,
    close_witnesses, condition_conjunction,
    data, graph, canonical_data,
    CanonicalGraph.Binary.data,
    CanonicalGraph.Binary.graph,
    witness_term, union_term, unordered_pair_term,
    source_id, witness_id]

/-- 基理论逐点证明编译后的二元并定义公式。 -/
private theorem compiled_definition_point_derives :
    Derives binary_union_base_theory []
      compiled_definition_point := by
  unfold compiled_definition_point
  let witness := witness_term (x#1) (x#3)
  have hWitness :
      Term.Admissible witness SetSort.set := by
    simpa [witness, witness_term] using
      union_term_admissible
        (unordered_pair_term (x#1) (x#3))
        (unordered_pair_term_admissible
          (x#1) (x#3)
          (set_variable_admissible 1)
          (set_variable_admissible 3))
  nd_apply Derives.exists_intro (term := witness)
  simpa [witness, graph, canonical_data,
      CanonicalGraph.Binary.graph, witness_term,
      union_term, unordered_pair_term,
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.substituteFree, Term.substituteFree] using
    Derives.conj_intro
      (Derives.eq_refl_m
        (T := binary_union_base_theory) (Γ := [])
        witness (sort := SetSort.set)
        (hTermCheck :=
          Term.check_certificate_of_admissible hWitness))
      (Derives.eq_refl_m
        (T := binary_union_base_theory) (Γ := [])
        witness (sort := SetSort.set)
        (hTermCheck :=
          Term.check_certificate_of_admissible hWitness))

/--
配对与一元并描述符理论的固定公理都不含二元并函数，故编译后保持原闭句不变。
-/
private theorem formula_base_eq
    {source : SetFormula}
    (hSource : binary_union_base_theory source) :
    FunctionGraphElimination.formula data source = source := by
  apply formula_eq_of_sentence_avoids data source
  · rcases hSource with hSource | hSource
    · rcases hSource with rfl | hSource
      · simpa [data, canonical_data,
            CanonicalGraph.Binary.data,
            pair_definition_axiom] using
          formula_avoids_forall_close
            FunctionSymbol.binaryUnion
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
              CanonicalGraph.Binary.data,
              pairing_axiom] using
            formula_avoids_forall_close
              FunctionSymbol.binaryUnion
              [(SetSort.set, 0), (SetSort.set, 1)]
              (pair_exists (x#0) (x#1)) <| by
                simp [pair_exists,
                  pair_member_condition,
                  FormulaAvoids, TermsAvoid, TermAvoids]
        · change source = extensionality_axiom at hSource
          subst source
          simpa [data, canonical_data,
              CanonicalGraph.Binary.data,
              extensionality_axiom] using
            formula_avoids_forall_close
              FunctionSymbol.binaryUnion
              [(SetSort.set, 0), (SetSort.set, 1)]
              (extensionality_instance
                (x#0) (x#1)) <| by
                  simp [extensionality_instance,
                    agreement_to_equality,
                    membership_agreement,
                    FormulaAvoids, TermsAvoid, TermAvoids]
    · rcases hSource with rfl | hSource
      · simpa [data, canonical_data,
            CanonicalGraph.Binary.data,
            union_definition_axiom] using
          formula_avoids_forall_close
            FunctionSymbol.binaryUnion
            [(SetSort.set, 0)]
            (union_definition_instance (x#0)) <| by
              simp [union_definition_instance,
                union_spec, union_term,
                FormulaAvoids, TermsAvoid, TermAvoids]
      · rcases hSource with rfl | hSource
        · simpa [data, canonical_data,
              CanonicalGraph.Binary.data,
              union_axiom] using
            formula_avoids_forall_close
              FunctionSymbol.binaryUnion
              [(SetSort.set, 0)]
              (union_exists (x#0)) <| by
                simp [union_exists,
                  FormulaAvoids, TermsAvoid, TermAvoids]
        · change source = extensionality_axiom at hSource
          subst source
          simpa [data, canonical_data,
              CanonicalGraph.Binary.data,
              extensionality_axiom] using
            formula_avoids_forall_close
              FunctionSymbol.binaryUnion
              [(SetSort.set, 0), (SetSort.set, 1)]
              (extensionality_instance
                (x#0) (x#1)) <| by
                  simp [extensionality_instance,
                    agreement_to_equality,
                    membership_agreement,
                    FormulaAvoids, TermsAvoid, TermAvoids]
  · exact binary_union_operator_theory_sentence
      (Or.inr hSource)

/-- 基理论证明完整二元并定义公理的函数图编译。 -/
private theorem formula_definition_axiom_derives :
    Derives binary_union_base_theory []
      (FunctionGraphElimination.formula
        data binary_union_definition_axiom) := by
  have hPoint :
      Derives binary_union_base_theory []
        (FunctionGraphElimination.formula
          data definition_point) := by
    rw [formula_definition_point]
    exact compiled_definition_point_derives
  have hPointAdmissible :
      Formula.Admissible definition_point :=
    binary_union_definition_instance_admissible
      (set_variable_admissible 0)
      (set_variable_admissible 1)
  have hRight :=
    graph_presentation.formula_forall_close_derives
      SetSort.set 1 definition_point
      hPointAdmissible hPoint
  have hRightAdmissible :
      Formula.Admissible
        (Formula.forallE SetSort.set
          (Formula.closeFreeAt SetSort.set
            1 0 definition_point)) :=
    Formula.Admissible.forall_closeFreeAt
      SetSort.set 1 hPointAdmissible
  have hLeft :=
    graph_presentation.formula_forall_close_derives
      SetSort.set 0
      (Formula.forallE SetSort.set
        (Formula.closeFreeAt SetSort.set
          1 0 definition_point))
      hRightAdmissible hRight
  simpa [binary_union_definition_axiom,
    definition_point] using hLeft

private theorem compile_axiom
    {source : SetFormula}
    (hSource : binary_union_operator_theory source) :
    Derives binary_union_base_theory []
      (FunctionGraphElimination.formula data source) := by
  rcases hSource with rfl | hSource
  · exact formula_definition_axiom_derives
  · rw [formula_base_eq hSource]
    exact Derives.theory_mem hSource
      (hFormulaCheck :=
        Formula.check_certificate_of_admissible
          (binary_union_base_theory_admissible
            source hSource))

/-- 二元并函数扩张的理论级函数图消去表示。 -/
def theory_presentation : TheoryPresentation data where
  graph := graph_presentation
  source := binary_union_operator_theory
  compile_axiom := compile_axiom

theorem hilbert
    {source : SetFormula}
    (hSource :
      HilbertDerives binary_union_operator_theory source) :
    Derives binary_union_base_theory []
      (FunctionGraphElimination.formula data source) :=
  theory_presentation.hilbert hSource

/-- 二元并扩张的 checked 自然演绎证明可整体翻译到其基理论。 -/
theorem derives
    {source : SetFormula}
    (hSource :
      Derives binary_union_operator_theory [] source) :
    Derives binary_union_base_theory []
      (FunctionGraphElimination.formula data source) :=
  theory_presentation.derives SetSort.set hSource

theorem hilbert_falsum
    (hSource :
      HilbertDerives binary_union_operator_theory
        Formula.falsum) :
    Derives binary_union_base_theory []
      Formula.falsum :=
  theory_presentation.hilbert_falsum hSource

theorem derives_falsum
    (hSource :
      Derives binary_union_operator_theory []
        Formula.falsum) :
    Derives binary_union_base_theory []
      Formula.falsum :=
  theory_presentation.derives_falsum
    SetSort.set hSource

theorem consistent
    (hBase :
      Derives.Consistent binary_union_base_theory []) :
    Derives.Consistent binary_union_operator_theory [] :=
  theory_presentation.consistent SetSort.set hBase

theorem hilbert_consistent
    (hBase :
      Derives.Consistent binary_union_base_theory []) :
    ¬ HilbertDerives binary_union_operator_theory
        Formula.falsum :=
  theory_presentation.hilbert_consistent hBase

private theorem realizes
    {arguments : List SetTerm}
    (hArguments :
      ArgsAdmissible arguments
        (signature.funcDomain FunctionSymbol.binaryUnion)) :
    Derives binary_union_operator_theory [] <|
      graph arguments
        (.app FunctionSymbol.binaryUnion arguments) := by
  change ArgsAdmissible arguments
    [SetSort.set, SetSort.set] at hArguments
  rcases pair_admissible hArguments with
    ⟨left, right, rfl, hLeft, hRight⟩
  simpa [graph, canonical_data,
      CanonicalGraph.Binary.graph,
      binary_union_term, witness_term] using
    binary_union_term_eq_union_pair_derives
      left right hLeft hRight

/-- 二元并函数定义扩张的完整函数图表示。 -/
def presentation : DefinitionPresentation data where
  toGraphPresentation := graph_presentation
  extension := binary_union_operator_theory
  extension_sentence := binary_union_operator_theory_sentence
  base_subset := by
    intro φ hφ
    exact Or.inr hφ
  realizes := realizes

theorem sentence_iff
    {source : SetFormula}
    (hSource : Formula.Sentence source) :
    Derives binary_union_operator_theory []
      (Formula.iff
        (FunctionGraphElimination.formula data source)
        source) :=
  presentation.sentence_iff hSource

end BinaryUnion
end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
