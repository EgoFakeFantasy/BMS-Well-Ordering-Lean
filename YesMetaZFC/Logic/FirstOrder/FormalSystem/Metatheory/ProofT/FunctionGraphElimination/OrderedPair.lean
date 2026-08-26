import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Canonical
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Singleton
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.RelationFunction.Core

/-!
# 有序对函数图消去实例

有序对函数以 Kuratowski 复合项 `{{a}, {a,b}}` 为规范图。图本身只使用已经位于
下层理论中的单点集与无序对函数；现有 `ordered_pair_spec` 定义公理与该规范图的
等价性由无序对规格合同给出。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace FunctionGraphElimination
namespace OrderedPair

open Nonlogical.BasicSetTheory
open scoped Symbols

set_option autoImplicit false

/-- Kuratowski 有序对的下层复合项。 -/
def kuratowski_term (left right : SetTerm) : SetTerm :=
  unordered_pair_term
    (singleton_term left)
    (unordered_pair_term left right)

private theorem kuratowski_well_sorted
    {left right : SetTerm}
    (hLeft : TermWellSorted left SetSort.set)
    (hRight : TermWellSorted right SetSort.set) :
    TermWellSorted (kuratowski_term left right)
      SetSort.set := by
  have hSingleton :
      TermWellSorted (singleton_term left) SetSort.set := by
    simpa [singleton_term, signature] using
      (TermWellSorted.app
        (σ := signature) FunctionSymbol.singleton
        (ArgsWellSorted.cons hLeft ArgsWellSorted.nil))
  have hPair :
      TermWellSorted (unordered_pair_term left right)
        SetSort.set := by
    simpa [unordered_pair_term, signature] using
      (TermWellSorted.app
        (σ := signature) FunctionSymbol.unorderedPair
        (ArgsWellSorted.cons hLeft
          (ArgsWellSorted.cons hRight ArgsWellSorted.nil)))
  simpa [kuratowski_term, unordered_pair_term, signature] using
    (TermWellSorted.app
      (σ := signature) FunctionSymbol.unorderedPair
      (ArgsWellSorted.cons hSingleton
        (ArgsWellSorted.cons hPair ArgsWellSorted.nil)))

private theorem kuratowski_scoped
    {scope : Scope signature} {left right : SetTerm}
    (hLeft : TermScoped scope left)
    (hRight : TermScoped scope right) :
    TermScoped scope (kuratowski_term left right) := by
  have hSingleton :
      TermScoped scope (singleton_term left) := by
    simpa [singleton_term] using
      (TermScoped.app
        (σ := signature) (ctx := scope)
        FunctionSymbol.singleton [left] (by
          intro term hTerm
          rw [List.mem_singleton.mp hTerm]
          exact hLeft))
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
  simpa [kuratowski_term, unordered_pair_term] using
    (TermScoped.app
      (σ := signature) (ctx := scope)
      FunctionSymbol.unorderedPair
      [singleton_term left, unordered_pair_term left right] (by
        intro term hTerm
        rcases List.mem_cons.mp hTerm with rfl | hTerm
        · exact hSingleton
        · rw [List.mem_singleton.mp hTerm]
          exact hPair))

private theorem kuratowski_freeSupport
    {left right : SetTerm}
    {freeVariable : FreeVariable signature}
    (hMember :
      freeVariable ∈
        Term.freeSupport (kuratowski_term left right)) :
    freeVariable ∈ Term.freeSupport left ∨
      freeVariable ∈ Term.freeSupport right := by
  simpa [kuratowski_term, singleton_term,
    unordered_pair_term, Term.freeSupport,
    Term.freeSupportList, or_assoc] using hMember

private theorem kuratowski_substituteFree
    (target : SetSort) (id : FreeVarId)
    (replacement left right : SetTerm) :
    kuratowski_term
        (Term.substituteFree target id replacement left)
        (Term.substituteFree target id replacement right) =
      Term.substituteFree target id replacement
        (kuratowski_term left right) := by
  cases target
  simp [kuratowski_term, singleton_term,
    unordered_pair_term, Term.substituteFree]

private theorem kuratowski_avoids
    {left right : SetTerm}
    (hLeft :
      TermAvoids FunctionSymbol.orderedPair left)
    (hRight :
      TermAvoids FunctionSymbol.orderedPair right) :
    TermAvoids FunctionSymbol.orderedPair
      (kuratowski_term left right) := by
  simp [kuratowski_term, singleton_term,
    unordered_pair_term, TermAvoids, hLeft, hRight]

/-- 有序对函数由下层 Kuratowski 项直接给出的规范图数据。 -/
def canonical_data :
    CanonicalGraph.Binary signature where
  symbol := FunctionSymbol.orderedPair
  leftSort := SetSort.set
  rightSort := SetSort.set
  resultSort := SetSort.set
  domain_eq := rfl
  codomain_eq := rfl
  canonical := kuratowski_term
  canonical_well_formed := kuratowski_well_sorted
  canonical_scoped := kuratowski_scoped
  canonical_freeSupport := kuratowski_freeSupport
  canonical_substituteFree := kuratowski_substituteFree
  canonical_avoids := kuratowski_avoids

/-- 二元有序对图；错误元数在良构分支外落到假。 -/
def graph : List SetTerm → SetTerm → SetFormula :=
  canonical_data.graph

/-- 已实现的有序对函数图消去数据。 -/
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

/-- 单点集函数理论给出的全体、单值 Kuratowski 图表示。 -/
def graph_presentation : GraphPresentation data :=
  canonical_data.graph_presentation
    singleton_operator_theory
    singleton_operator_theory_sentence

/-- 规范图与仓库既有有序对规格在任意上下文中等价。 -/
private theorem graph_iff_spec
    {Γ : Context signature}
    (left right candidate : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    Derives singleton_operator_theory Γ <|
      Formula.iff (graph [left, right] candidate)
        (ordered_pair_spec left right candidate) := by
  have hBase :
      Derives pairing_operator_theory [] <|
        Formula.iff (graph [left, right] candidate)
          (ordered_pair_spec left right candidate) := by
    simpa [graph, kuratowski_term, ordered_pair_spec] using
      unordered_pair_eq_iff_spec
        (singleton_term left)
        (unordered_pair_term left right)
        candidate
        (singleton_term_admissible left hLeft)
        (unordered_pair_term_admissible
          left right hLeft hRight)
        hCandidate
  exact (Derives.theory_weaken
    (T := pairing_operator_theory)
    (U := singleton_operator_theory)
    (fun _ hφ => Or.inr hφ) hBase).context_weaken
      (Δ := Γ) (by
        intro source hSource
        cases hSource)

/-- 三个外层 binder 打开后的有序对定义实例。 -/
private def definition_point : SetFormula :=
  ordered_pair_definition_instance
    (x#0) (x#1) (x#2)

/-- 开放定义实例消去有序对函数后的显式图正规形。 -/
private def compiled_definition_point : SetFormula :=
  ((∃ₘ[SetSort.set, 0],
      graph [x#1, x#3] (x#0) ∧ₘ
        ((x#5) ≐ₘ (x#0))) ↔ₘ
    ordered_pair_spec (x#1) (x#3) (x#5))

/-- 不含有序对函数的规格只执行奇数区变量重编码。 -/
private theorem formula_ordered_pair_spec_point :
    FunctionGraphElimination.formula data
        (ordered_pair_spec (x#0) (x#1) (x#2)) =
      ordered_pair_spec (x#1) (x#3) (x#5) := by
  rw [formula_eq_source_of_avoids]
  · simp [source_formula, source_term,
      ordered_pair_spec, pair_spec,
      pair_member_condition, singleton_term,
      unordered_pair_term, source_id]
  · simp [ordered_pair_spec, pair_spec,
      pair_member_condition, singleton_term,
      unordered_pair_term,
      FormulaAvoids, TermsAvoid, TermAvoids,
      data, canonical_data, CanonicalGraph.Binary.data]

/-- 开放定义实例的编译只生成一个 Kuratowski 图见证。 -/
private theorem formula_definition_point :
    FunctionGraphElimination.formula data definition_point =
      compiled_definition_point := by
  unfold definition_point
    ordered_pair_definition_instance
  rw [FunctionGraphElimination.formula]
  rw [formula_ordered_pair_spec_point]
  simp [compiled_definition_point,
    FunctionGraphElimination.formula,
    FunctionGraphElimination.equality,
    FunctionGraphElimination.terms,
    FunctionGraphElimination.term,
    close_witnesses, condition_conjunction,
    data, graph, canonical_data,
    CanonicalGraph.Binary.data,
    CanonicalGraph.Binary.graph,
    source_id, witness_id]

private theorem theory_fresh
    (id : FreeVarId) :
    ∀ source, singleton_operator_theory source →
      (SetSort.set, id) ∉ Formula.freeSupport source := by
  intro source hSource
  rw [(graph_presentation.theory_sentence hSource).2]
  exact List.not_mem_nil

/-- 单点集函数理论逐点证明编译后的有序对定义公式。 -/
private theorem compiled_definition_point_derives :
    Derives singleton_operator_theory []
      compiled_definition_point := by
  unfold compiled_definition_point
  let arguments : List SetTerm := [x#1, x#3]
  let graphBody := graph arguments (x#0)
  have hArguments :
      ArgsAdmissible arguments
        [SetSort.set, SetSort.set] :=
    ArgsAdmissible.cons
      (set_variable_admissible 1)
      (ArgsAdmissible.cons
        (set_variable_admissible 3)
        ArgsAdmissible.nil)
  have hZero :
      Term.Admissible (x#0) SetSort.set :=
    set_variable_admissible 0
  have hFive :
      Term.Admissible (x#5) SetSort.set :=
    set_variable_admissible 5
  apply Derives.iff_intro
  ·
    let body :=
      Formula.conj graphBody ((x#5) ≐ₘ (x#0))
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
    · simpa [body, graphBody, arguments] using
        (Derives.assumption_of_mem (by simp) :
          Derives singleton_operator_theory
            [∃ₘ[SetSort.set, 0], body]
            (∃ₘ[SetSort.set, 0], body))
    · have hBody :
          Derives singleton_operator_theory
            [body, ∃ₘ[SetSort.set, 0], body] body :=
        Derives.assumption_of_mem (by simp)
      have hWitnessGraph :=
        Derives.conj_elim_left hBody
      have hEquality :=
        Derives.conj_elim_right hBody
      have hCandidateGraph :
          Derives singleton_operator_theory
            [body, ∃ₘ[SetSort.set, 0], body]
            (graph [x#1, x#3] (x#5)) := by
        have hResult :=
          graph_presentation.graph_result_congr
            hArguments hZero hFive
            (Metatheory.Derives.equality_symm hEquality)
        exact Derives.iff_elim_right
          hResult hWitnessGraph
      exact Derives.iff_elim_right
        (graph_iff_spec
          (Γ := [body, ∃ₘ[SetSort.set, 0], body])
          (x#1) (x#3) (x#5)
          (set_variable_admissible 1)
          (set_variable_admissible 3)
          hFive)
        hCandidateGraph
  ·
    have hSpec :
        Derives singleton_operator_theory
          [ordered_pair_spec (x#1) (x#3) (x#5)]
          (ordered_pair_spec (x#1) (x#3) (x#5)) :=
      Derives.assumption_of_mem (by simp)
    have hCandidateGraph :
        Derives singleton_operator_theory
          [ordered_pair_spec (x#1) (x#3) (x#5)]
          (graph [x#1, x#3] (x#5)) :=
      Derives.iff_elim_left
        (graph_iff_spec
          (Γ := [ordered_pair_spec
            (x#1) (x#3) (x#5)])
          (x#1) (x#3) (x#5)
          (set_variable_admissible 1)
          (set_variable_admissible 3)
          hFive)
        hSpec
    nd_apply Derives.exists_intro (term := x#5)
    simpa [graphBody, arguments, graph,
      canonical_data, CanonicalGraph.Binary.graph,
      kuratowski_term, singleton_term,
      unordered_pair_term,
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.substituteFree, Term.substituteFree] using
      Derives.conj_intro hCandidateGraph
        (Derives.eq_refl_m
          (T := singleton_operator_theory)
          (Γ := [ordered_pair_spec
            (x#1) (x#3) (x#5)])
          (x#5))

/-- 单点集函数理论中的公理不含有序对函数，故编译后严格保持不变。 -/
private theorem formula_base_eq
    {source : SetFormula}
    (hSource : singleton_operator_theory source) :
    FunctionGraphElimination.formula data source = source := by
  apply formula_eq_of_sentence_avoids data source
  · rcases hSource with rfl | hSource
    · simpa [singleton_definition_axiom] using
        formula_avoids_forall_close
          FunctionSymbol.orderedPair
          [(SetSort.set, 0)]
          (singleton_definition_instance (x#0)) <| by
            simp [singleton_definition_instance,
              singleton_term, unordered_pair_term,
              FormulaAvoids, TermAvoids]
    · rcases hSource with rfl | hSource
      · simpa [pair_definition_axiom] using
          formula_avoids_forall_close
            FunctionSymbol.orderedPair
            [(SetSort.set, 0), (SetSort.set, 1),
              (SetSort.set, 2)]
            (pair_definition_instance
              (x#0) (x#1) (x#2)) <| by
                simp [pair_definition_instance,
                  pair_spec, pair_member_condition,
                  unordered_pair_term,
                  FormulaAvoids, TermsAvoid, TermAvoids]
      · rcases hSource with rfl | hSource
        · simpa [pairing_axiom] using
            formula_avoids_forall_close
              FunctionSymbol.orderedPair
              [(SetSort.set, 0), (SetSort.set, 1)]
              (pair_exists (x#0) (x#1)) <| by
                simp [pair_exists, pair_member_condition,
                  FormulaAvoids, TermsAvoid, TermAvoids]
        · change source = extensionality_axiom at hSource
          subst source
          simpa [extensionality_axiom] using
            formula_avoids_forall_close
              FunctionSymbol.orderedPair
              [(SetSort.set, 0), (SetSort.set, 1)]
              (extensionality_instance
                (x#0) (x#1)) <| by
                  simp [extensionality_instance,
                    agreement_to_equality,
                    membership_agreement,
                    FormulaAvoids, TermsAvoid, TermAvoids]
  · exact singleton_operator_theory_sentence hSource

/-- 单点集函数理论证明整个有序对定义公理的函数图编译。 -/
private theorem formula_definition_axiom_derives :
    Derives singleton_operator_theory []
      (FunctionGraphElimination.formula
        data ordered_pair_definition_axiom) := by
  have hPoint :
      Derives singleton_operator_theory []
        (FunctionGraphElimination.formula
          data definition_point) := by
    rw [formula_definition_point]
    exact compiled_definition_point_derives
  have hPointAdmissible :
      Formula.Admissible definition_point :=
    ordered_pair_definition_instance_admissible
      (set_variable_admissible 0)
      (set_variable_admissible 1)
      (set_variable_admissible 2)
  have hCandidate :=
    graph_presentation.formula_forall_close_derives
      SetSort.set 2 definition_point
      hPointAdmissible hPoint
  have hCandidateAdmissible :
      Formula.Admissible
        (Formula.forallE SetSort.set
          (Formula.closeFreeAt SetSort.set
            2 0 definition_point)) :=
    Formula.Admissible.forall_closeFreeAt
      SetSort.set 2 hPointAdmissible
  have hRight :=
    graph_presentation.formula_forall_close_derives
      SetSort.set 1
      (Formula.forallE SetSort.set
        (Formula.closeFreeAt SetSort.set
          2 0 definition_point))
      hCandidateAdmissible hCandidate
  have hRightAdmissible :
      Formula.Admissible
        (Formula.forallE SetSort.set
          (Formula.closeFreeAt SetSort.set 1 0
            (Formula.forallE SetSort.set
              (Formula.closeFreeAt SetSort.set
                2 0 definition_point)))) :=
    Formula.Admissible.forall_closeFreeAt
      SetSort.set 1 hCandidateAdmissible
  have hLeft :=
    graph_presentation.formula_forall_close_derives
      SetSort.set 0
      (Formula.forallE SetSort.set
        (Formula.closeFreeAt SetSort.set 1 0
          (Formula.forallE SetSort.set
            (Formula.closeFreeAt SetSort.set
              2 0 definition_point))))
      hRightAdmissible hRight
  simpa [ordered_pair_definition_axiom,
    definition_point] using hLeft

private theorem compile_axiom
    {source : SetFormula}
    (hSource : ordered_pair_operator_theory source) :
    Derives singleton_operator_theory []
      (FunctionGraphElimination.formula data source) := by
  rcases hSource with rfl | hSource
  · exact formula_definition_axiom_derives
  · rw [formula_base_eq hSource]
    exact Derives.theory_mem hSource
      (hFormulaCheck :=
        Formula.check_certificate_of_admissible
          (singleton_operator_theory_admissible
            source hSource))

/-- 有序对函数扩张的理论级函数图消去表示。 -/
def theory_presentation : TheoryPresentation data where
  graph := graph_presentation
  source := ordered_pair_operator_theory
  compile_axiom := compile_axiom

theorem hilbert
    {source : SetFormula}
    (hSource :
      HilbertDerives ordered_pair_operator_theory source) :
    Derives singleton_operator_theory []
      (FunctionGraphElimination.formula data source) :=
  theory_presentation.hilbert hSource

/-- 有序对函数扩张的 checked 自然演绎证明可整体翻译到单点集函数理论。 -/
theorem derives
    {source : SetFormula}
    (hSource :
      Derives ordered_pair_operator_theory [] source) :
    Derives singleton_operator_theory []
      (FunctionGraphElimination.formula data source) :=
  theory_presentation.derives SetSort.set hSource

theorem hilbert_falsum
    (hSource :
      HilbertDerives ordered_pair_operator_theory
        Formula.falsum) :
    Derives singleton_operator_theory []
      Formula.falsum :=
  theory_presentation.hilbert_falsum hSource

theorem derives_falsum
    (hSource :
      Derives ordered_pair_operator_theory []
        Formula.falsum) :
    Derives singleton_operator_theory []
      Formula.falsum :=
  theory_presentation.derives_falsum
    SetSort.set hSource

theorem consistent
    (hBase :
      Derives.Consistent singleton_operator_theory []) :
    Derives.Consistent ordered_pair_operator_theory [] :=
  theory_presentation.consistent SetSort.set hBase

theorem hilbert_consistent
    (hBase :
      Derives.Consistent singleton_operator_theory []) :
    ¬ HilbertDerives ordered_pair_operator_theory
        Formula.falsum :=
  theory_presentation.hilbert_consistent hBase

private theorem realizes
    {arguments : List SetTerm}
    (hArguments :
      ArgsAdmissible arguments
        (signature.funcDomain FunctionSymbol.orderedPair)) :
    Derives ordered_pair_operator_theory [] <|
      graph arguments
        (.app FunctionSymbol.orderedPair arguments) := by
  change ArgsAdmissible arguments
    [SetSort.set, SetSort.set] at hArguments
  rcases pair_admissible hArguments with
    ⟨left, right, rfl, hLeft, hRight⟩
  have hSpec :
      Derives ordered_pair_operator_theory []
        (ordered_pair_spec left right
          (ordered_pair_term left right)) :=
    ordered_pair_term_spec_derives
      left right hLeft hRight
  have hBridge :
      Derives ordered_pair_operator_theory [] <|
        Formula.iff
          (graph [left, right]
            (ordered_pair_term left right))
          (ordered_pair_spec left right
            (ordered_pair_term left right)) :=
    Derives.theory_weaken
      (T := singleton_operator_theory)
      (U := ordered_pair_operator_theory)
      (fun _ hφ => Or.inr hφ)
      (graph_iff_spec
        (Γ := []) left right
        (ordered_pair_term left right)
        hLeft hRight
        (ordered_pair_term_admissible
          left right hLeft hRight))
  simpa [ordered_pair_term] using
    Derives.iff_elim_left hBridge hSpec

/-- 有序对函数定义扩张的完整函数图表示。 -/
def presentation : DefinitionPresentation data where
  toGraphPresentation := graph_presentation
  extension := ordered_pair_operator_theory
  extension_sentence :=
    ordered_pair_operator_theory_sentence
  base_subset := by
    intro φ hφ
    exact Or.inr hφ
  realizes := realizes

theorem sentence_iff
    {source : SetFormula}
    (hSource : Formula.Sentence source) :
    Derives ordered_pair_operator_theory []
      (Formula.iff
        (FunctionGraphElimination.formula data source)
        source) :=
  presentation.sentence_iff hSource

end OrderedPair
end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
