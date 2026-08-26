import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Canonical
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Intersection.Derived

/-
# 二元交函数图消去实例

二元交由下层无序对与一元交规范项给出。这里不重新证明交集的存在性，
而是把已有的规范项描述接入统一的 `CanonicalGraph.Binary` 编译器。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace FunctionGraphElimination
namespace BinaryIntersection

open Nonlogical.BasicSetTheory
open scoped Symbols

set_option autoImplicit false

/-- 二元交定义右侧的下层规范项。 -/
def witness_term (left right : SetTerm) : SetTerm :=
  intersection_term (unordered_pair_term left right)

private theorem witness_well_sorted
    {left right : SetTerm}
    (hLeft : TermWellSorted left SetSort.set)
    (hRight : TermWellSorted right SetSort.set) :
    TermWellSorted (witness_term left right) SetSort.set := by
  have hPair :
      TermWellSorted (unordered_pair_term left right) SetSort.set := by
    simpa [unordered_pair_term, signature] using
      (TermWellSorted.app
        (σ := signature) FunctionSymbol.unorderedPair
        (ArgsWellSorted.cons hLeft
          (ArgsWellSorted.cons hRight ArgsWellSorted.nil)))
  simpa [witness_term, intersection_term, signature] using
    (TermWellSorted.app
      (σ := signature) FunctionSymbol.intersection
      (ArgsWellSorted.cons hPair ArgsWellSorted.nil))

private theorem witness_scoped
    {scope : Scope signature} {left right : SetTerm}
    (hLeft : TermScoped scope left)
    (hRight : TermScoped scope right) :
    TermScoped scope (witness_term left right) := by
  have hPair :
      TermScoped scope (unordered_pair_term left right) := by
    simpa [unordered_pair_term] using
      (TermScoped.app
        (σ := signature) (ctx := scope)
        FunctionSymbol.unorderedPair [left, right] (by
          intro term hTerm
          rcases List.mem_cons.mp hTerm with rfl | hTerm
          · exact hLeft
          · rw [List.mem_singleton.mp hTerm]
            exact hRight))
  simpa [witness_term, intersection_term] using
    (TermScoped.app
      (σ := signature) (ctx := scope)
      FunctionSymbol.intersection [unordered_pair_term left right] (by
        intro term hTerm
        rw [List.mem_singleton.mp hTerm]
        exact hPair))

private theorem witness_freeSupport
    {left right : SetTerm}
    {freeVariable : FreeVariable signature}
    (hMember :
      freeVariable ∈ Term.freeSupport (witness_term left right)) :
    freeVariable ∈ Term.freeSupport left ∨
      freeVariable ∈ Term.freeSupport right := by
  simpa [witness_term, intersection_term,
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
  simp [witness_term, intersection_term,
    unordered_pair_term, Term.substituteFree]

private theorem witness_avoids
    {left right : SetTerm}
    (hLeft : TermAvoids FunctionSymbol.binaryIntersection left)
    (hRight : TermAvoids FunctionSymbol.binaryIntersection right) :
    TermAvoids FunctionSymbol.binaryIntersection
      (witness_term left right) := by
  simp [witness_term, intersection_term,
    unordered_pair_term, TermAvoids, hLeft, hRight]

/-- 二元交函数的规范图数据。 -/
def canonical_data :
    CanonicalGraph.Binary signature where
  symbol := FunctionSymbol.binaryIntersection
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

/-- 二元交函数图；错误元数在良构分支外落到假。 -/
def graph : List SetTerm → SetTerm → SetFormula :=
  canonical_data.graph

/-- 已实现的二元交函数图消去数据。 -/
def data : Data signature :=
  canonical_data.data

private theorem pair_admissible
    {arguments : List SetTerm}
    (hArguments :
      ArgsAdmissible arguments [SetSort.set, SetSort.set]) :
    ∃ left right,
      arguments = [left, right] ∧
        Term.Admissible left SetSort.set ∧
        Term.Admissible right SetSort.set := by
  simpa [canonical_data] using
    canonical_data.arguments_admissible hArguments

/-- 配对与交集描述理论给出的全体、单值二元交图。 -/
def graph_presentation : GraphPresentation data :=
  canonical_data.graph_presentation
    binary_intersection_base_theory
    (by
      intro φ hφ
      rcases hφ with hφ | hφ
      · exact pairing_operator_theory_sentence hφ
      · exact intersection_operator_theory_sentence hφ)

private def definition_point : SetFormula :=
  binary_intersection_definition_instance (x#0) (x#1)

private def compiled_definition_point : SetFormula :=
  ∃ₘ[SetSort.set, 0],
    graph [x#1, x#3] (x#0) ∧ₘ
      ((x#0) ≐ₘ witness_term (x#1) (x#3))

private theorem formula_definition_point :
    FunctionGraphElimination.formula data definition_point =
      compiled_definition_point := by
  unfold definition_point
    binary_intersection_definition_instance
  rw [FunctionGraphElimination.formula]
  simp [compiled_definition_point,
    FunctionGraphElimination.equality,
    FunctionGraphElimination.term,
    FunctionGraphElimination.terms,
    close_witnesses, condition_conjunction,
    data, graph, canonical_data,
    CanonicalGraph.Binary.data,
    CanonicalGraph.Binary.graph,
    witness_term, intersection_term,
    unordered_pair_term, source_id, witness_id]

private theorem compiled_definition_point_derives :
    Derives binary_intersection_base_theory []
      compiled_definition_point := by
  unfold compiled_definition_point
  let witness := witness_term (x#1) (x#3)
  have hWitness :
      Term.Admissible witness SetSort.set := by
    simpa [witness, witness_term] using
      intersection_term_admissible
        (unordered_pair_term (x#1) (x#3))
        (unordered_pair_term_admissible
          (x#1) (x#3)
          (set_variable_admissible 1)
          (set_variable_admissible 3))
  nd_apply Derives.exists_intro (term := witness)
  simpa [witness, graph, canonical_data,
      CanonicalGraph.Binary.graph, witness_term,
      intersection_term, unordered_pair_term,
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.substituteFree, Term.substituteFree] using
    Derives.conj_intro
      (Derives.eq_refl_m
        (T := binary_intersection_base_theory) (Γ := [])
        witness (sort := SetSort.set)
        (hTermCheck :=
          Term.check_certificate_of_admissible hWitness))
      (Derives.eq_refl_m
        (T := binary_intersection_base_theory) (Γ := [])
        witness (sort := SetSort.set)
        (hTermCheck :=
          Term.check_certificate_of_admissible hWitness))

private theorem formula_base_eq
    {source : SetFormula}
    (hSource : binary_intersection_base_theory source) :
    FunctionGraphElimination.formula data source = source := by
  apply formula_eq_of_sentence_avoids data source
  · apply checkFormulaAvoids_sound
    rcases hSource with hPair | hIntersection
    · rcases hPair with rfl | hPair
      · native_decide
      · rcases hPair with rfl | hExtensionality
        · native_decide
        · change source = extensionality_axiom at hExtensionality
          subst source
          native_decide
    · rcases hIntersection with rfl | hIntersectionBase
      · native_decide
      · rcases hIntersectionBase with rfl | hFoundations
        · native_decide
        · rcases hFoundations with hSubset | hEmpty
          · rcases hSubset with rfl | hExtensionality
            · native_decide
            · change source = extensionality_axiom at hExtensionality
              subst source
              native_decide
          · rcases hEmpty with rfl | hEmptyBase
            · native_decide
            · rcases hEmptyBase with rfl | hExtensionality
              · native_decide
              · change source = extensionality_axiom at hExtensionality
                subst source
                native_decide
  · exact binary_intersection_base_theory_sentence hSource

private theorem formula_definition_axiom_derives :
    Derives binary_intersection_base_theory []
      (FunctionGraphElimination.formula data
        binary_intersection_definition_axiom) := by
  have hPoint :
      Derives binary_intersection_base_theory []
        (FunctionGraphElimination.formula data
          definition_point) := by
    rw [formula_definition_point]
    exact compiled_definition_point_derives
  have hPointAdmissible :
      Formula.Admissible definition_point :=
    binary_intersection_definition_instance_admissible
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
  simpa [binary_intersection_definition_axiom,
    definition_point] using hLeft

private theorem compile_axiom
    {source : SetFormula}
    (hSource : binary_intersection_operator_theory source) :
    Derives binary_intersection_base_theory []
      (FunctionGraphElimination.formula data source) := by
  rcases hSource with rfl | hSource
  · exact formula_definition_axiom_derives
  · rw [formula_base_eq hSource]
    exact Derives.theory_mem hSource
      (hFormulaCheck :=
        Formula.check_certificate_of_admissible
          (binary_intersection_base_theory_admissible
            source hSource))

/-- 二元交函数扩张的理论级函数图消去表示。 -/
def theory_presentation : TheoryPresentation data where
  graph := graph_presentation
  source := binary_intersection_operator_theory
  compile_axiom := compile_axiom

theorem hilbert
    {source : SetFormula}
    (hSource :
      HilbertDerives binary_intersection_operator_theory source) :
    Derives binary_intersection_base_theory []
      (FunctionGraphElimination.formula data source) :=
  theory_presentation.hilbert hSource

theorem derives
    {source : SetFormula}
    (hSource :
      Derives binary_intersection_operator_theory [] source) :
    Derives binary_intersection_base_theory []
      (FunctionGraphElimination.formula data source) :=
  theory_presentation.derives SetSort.set hSource

theorem hilbert_falsum
    (hSource :
      HilbertDerives binary_intersection_operator_theory
        Formula.falsum) :
    Derives binary_intersection_base_theory []
      Formula.falsum :=
  theory_presentation.hilbert_falsum hSource

theorem derives_falsum
    (hSource :
      Derives binary_intersection_operator_theory []
        Formula.falsum) :
    Derives binary_intersection_base_theory []
      Formula.falsum :=
  theory_presentation.derives_falsum
    SetSort.set hSource

theorem consistent
    (hBase :
      Derives.Consistent binary_intersection_base_theory []) :
    Derives.Consistent binary_intersection_operator_theory [] :=
  theory_presentation.consistent SetSort.set hBase

theorem hilbert_consistent
    (hBase :
      Derives.Consistent binary_intersection_base_theory []) :
    ¬ HilbertDerives binary_intersection_operator_theory
        Formula.falsum :=
  theory_presentation.hilbert_consistent hBase

private theorem realizes
    {arguments : List SetTerm}
    (hArguments :
      ArgsAdmissible arguments
        (signature.funcDomain FunctionSymbol.binaryIntersection)) :
    Derives binary_intersection_operator_theory [] <|
      graph arguments
        (.app FunctionSymbol.binaryIntersection arguments) := by
  change ArgsAdmissible arguments
    [SetSort.set, SetSort.set] at hArguments
  rcases pair_admissible hArguments with
    ⟨left, right, rfl, hLeft, hRight⟩
  simpa [graph, canonical_data,
      CanonicalGraph.Binary.graph,
      binary_intersection_term, witness_term] using
    binary_intersection_term_eq_intersection_pair_derives
      left right hLeft hRight

/-- 二元交函数定义扩张的完整函数图表示。 -/
def presentation : DefinitionPresentation data where
  toGraphPresentation := graph_presentation
  extension := binary_intersection_operator_theory
  extension_sentence := binary_intersection_operator_theory_sentence
  base_subset := by
    intro φ hφ
    exact Or.inr hφ
  realizes := realizes

theorem sentence_iff
    {source : SetFormula}
    (hSource : Formula.Sentence source) :
    Derives binary_intersection_operator_theory []
      (Formula.iff
        (FunctionGraphElimination.formula data source)
        source) :=
  presentation.sentence_iff hSource

end BinaryIntersection
end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
