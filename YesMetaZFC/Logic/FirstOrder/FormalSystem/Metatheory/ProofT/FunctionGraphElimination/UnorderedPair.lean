import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Hilbert
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Pairing

/-!
# 无序对函数图消去实例

本模块以 `pair_spec` 为二元无序对函数的图，并把配对存在性与外延唯一性接入
证明级函数图编译器。定义公理的编译证明只消费这两个最弱集合论事实。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace FunctionGraphElimination
namespace UnorderedPair

open Nonlogical.BasicSetTheory
open scoped Symbols

set_option autoImplicit false

/-- 二元无序对图；错误元数在良构分支外落到假。 -/
def graph : List SetTerm → SetTerm → SetFormula
  | (left :: right :: []), result =>
      pair_spec left right result
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
          FunctionSymbol.unorderedPair))
    (hResult :
      TermWellSorted result SetSort.set) :
    FormulaWellFormed (graph arguments result) := by
  change ArgsWellSorted arguments
    [SetSort.set, SetSort.set] at hArguments
  cases hArguments with
  | cons hLeft hTail =>
      cases hTail with
      | cons hRight hNil =>
          cases hNil
          unfold graph pair_spec pair_member_condition
          apply FormulaWellFormed.forallE
          apply FormulaWellFormed.iff
          · apply FormulaWellFormed.rel
            simpa [signature] using
              ArgsWellSorted.cons
                (TermWellSorted.bvar
                  SetSort.set 0)
                (ArgsWellSorted.cons hResult
                  ArgsWellSorted.nil)
          · apply FormulaWellFormed.disj
            · exact FormulaWellFormed.equal
                (TermWellSorted.bvar
                  (σ := signature)
                  SetSort.set 0)
                hLeft
            · exact FormulaWellFormed.equal
                (TermWellSorted.bvar
                  (σ := signature)
                  SetSort.set 0)
                hRight

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
  | cons left tail =>
      cases tail with
      | nil =>
          simpa [graph] using
            (FormulaScoped.falsum :
              FormulaScoped scope
                (Formula.falsum : SetFormula))
      | cons right rest =>
          cases rest with
          | nil =>
              unfold graph pair_spec
                pair_member_condition
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
              · apply FormulaScoped.disj
                · exact FormulaScoped.equal
                    (TermScoped.bvar
                      (σ := signature) <| by
                        change
                          0 < Nat.succ
                            (scope SetSort.set)
                        exact Nat.zero_lt_succ _)
                    (push_scoped <|
                      hArguments left (by simp))
                · exact FormulaScoped.equal
                    (TermScoped.bvar
                      (σ := signature) <| by
                        change
                          0 < Nat.succ
                            (scope SetSort.set)
                        exact Nat.zero_lt_succ _)
                    (push_scoped <|
                      hArguments right (by simp))
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
  | cons left tail =>
      cases tail with
      | nil =>
          simp [graph, Formula.freeSupport] at hMember
      | cons right rest =>
          cases rest with
          | nil =>
              simpa [graph, pair_spec,
                pair_member_condition,
                Formula.freeSupport,
                Term.freeSupportList,
                Term.freeSupport, or_assoc,
                or_left_comm, or_comm] using
                  hMember
          | cons extra rest =>
              simp [graph, Formula.freeSupport]
                at hMember

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
  | cons left tail =>
      cases tail with
      | nil =>
          simp [graph, Formula.substituteFree]
      | cons right rest =>
          cases rest with
          | nil =>
              cases target
              simp [graph, pair_spec,
                pair_member_condition,
                Formula.substituteFree,
                Term.substituteFree]
          | cons extra rest =>
              simp [graph, Formula.substituteFree]

private theorem graph_avoids
    {arguments : List SetTerm} {result : SetTerm}
    (hArguments :
      TermsAvoid FunctionSymbol.unorderedPair
        arguments)
    (hResult :
      TermAvoids FunctionSymbol.unorderedPair
        result) :
    FormulaAvoids FunctionSymbol.unorderedPair
      (graph arguments result) := by
  cases arguments with
  | nil =>
      simp [graph, FormulaAvoids]
  | cons left tail =>
      cases tail with
      | nil =>
          simp [graph, FormulaAvoids]
      | cons right rest =>
          cases rest with
          | nil =>
              change
                TermsAvoid
                    FunctionSymbol.unorderedPair
                    [(Term.var
                        (.bvar SetSort.set 0) :
                          SetTerm),
                      result] ∧
                  ((TermAvoids
                      FunctionSymbol.unorderedPair
                      (Term.var
                        (.bvar SetSort.set 0) :
                          SetTerm) ∧
                    TermAvoids
                      FunctionSymbol.unorderedPair
                      left) ∧
                  (TermAvoids
                      FunctionSymbol.unorderedPair
                      (Term.var
                        (.bvar SetSort.set 0) :
                          SetTerm) ∧
                    TermAvoids
                      FunctionSymbol.unorderedPair
                      right))
              have hLeft :=
                hArguments left (by simp)
              have hRight :=
                hArguments right (by simp)
              simp [TermsAvoid, TermAvoids,
                hResult, hLeft, hRight]
          | cons extra rest =>
              simp [graph, FormulaAvoids]

/-- 已实现的无序对函数图消去数据。 -/
def data : Data signature where
  symbol := FunctionSymbol.unorderedPair
  sort := SetSort.set
  codomain_eq := rfl
  graph := UnorderedPair.graph
  graph_well_formed := graph_well_formed
  graph_scoped := graph_scoped
  graph_freeSupport := graph_freeSupport
  graph_substituteFree := graph_substituteFree
  graph_avoids := graph_avoids

private theorem pair_admissible
    {arguments : List SetTerm}
    (hArguments :
      ArgsAdmissible arguments
        [SetSort.set, SetSort.set]) :
    ∃ left right,
      arguments = [left, right] ∧
        Term.Admissible left SetSort.set ∧
        Term.Admissible right SetSort.set := by
  rcases hArguments with
    ⟨hSorted, hScoped⟩
  cases hSorted with
  | cons hLeft hTail =>
      cases hTail with
      | cons hRight hNil =>
          cases hNil
          exact ⟨_, _, rfl,
            ⟨hLeft, hScoped _ (by simp)⟩,
            ⟨hRight, hScoped _ (by simp)⟩⟩

private theorem total
    {arguments : List SetTerm}
    (resultId : FreeVarId)
    (hArguments :
      ArgsAdmissible arguments
        (signature.funcDomain
          FunctionSymbol.unorderedPair))
    (hFresh :
      (SetSort.set, resultId) ∉
        Term.freeSupportList arguments) :
    Derives pairing_theory [] <|
      Formula.existsE SetSort.set <|
        Formula.closeFreeAt SetSort.set resultId 0 <|
          graph arguments <|
            .var (.fvar SetSort.set resultId) := by
  change ArgsAdmissible arguments
    [SetSort.set, SetSort.set] at hArguments
  rcases pair_admissible hArguments with
    ⟨left, right, rfl, hLeft, hRight⟩
  simp only [Term.freeSupportList,
    List.append_nil] at hFresh
  have hLeftFresh :
      (SetSort.set, resultId) ∉
        Term.freeSupport left := by
    intro hMember
    apply hFresh
    change
      (SetSort.set, resultId) ∈
        Term.freeSupport left ++
          Term.freeSupport right
    exact List.mem_append.mpr (Or.inl hMember)
  have hRightFresh :
      (SetSort.set, resultId) ∉
        Term.freeSupport right := by
    intro hMember
    apply hFresh
    change
      (SetSort.set, resultId) ∈
        Term.freeSupport left ++
          Term.freeSupport right
    exact List.mem_append.mpr (Or.inr hMember)
  have hLeftClose :
      Term.closeFreeAt SetSort.set resultId 1 left =
        left :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set resultId 1 left
      hLeft.2 hLeftFresh
  have hRightClose :
      Term.closeFreeAt SetSort.set resultId 1 right =
        right :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set resultId 1 right
      hRight.2 hRightFresh
  simpa [graph, pair_exists, pair_spec,
    pair_member_condition,
    Formula.closeFreeAt, Formula.next_depth,
    Term.closeFreeAt, hLeftClose,
    hRightClose] using
    pair_exists_derives
      left right hLeft hRight

private theorem functional
    {arguments : List SetTerm}
    {left right : SetTerm}
    (hArguments :
      ArgsAdmissible arguments
        (signature.funcDomain
          FunctionSymbol.unorderedPair))
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    Derives pairing_theory [] <|
      Formula.imp (graph arguments left) <|
        Formula.imp (graph arguments right) <|
          Formula.equal left right := by
  change ArgsAdmissible arguments
    [SetSort.set, SetSort.set] at hArguments
  rcases pair_admissible hArguments with
    ⟨first, second, rfl, hFirst, hSecond⟩
  apply Derives.theory_weaken
    (T := extensionality_theory)
  · intro φ hφ
    exact Or.inr hφ
  · simpa [graph] using
      pair_unique first second left right
        hFirst hSecond hLeft hRight

/-- 配对存在理论给出的全体、单值无序对图表示。 -/
def graph_presentation : GraphPresentation data where
  theory := pairing_theory
  theory_sentence := by
    intro φ hφ
    exact pairing_operator_theory_sentence
      (Or.inr hφ)
  total := total
  functional := functional

/-- 三个外层 binder 打开后的无序对定义实例。 -/
private def definition_point : SetFormula :=
  pair_definition_instance
    (x#0) (x#1) (x#2)

/-- 开放定义实例消去无序对函数后的显式图正规形。 -/
private def compiled_definition_point : SetFormula :=
  ((∃ₘ[SetSort.set, 0],
      pair_spec (x#1) (x#3) (x#0) ∧ₘ
        ((x#5) ≐ₘ (x#0))) ↔ₘ
    pair_spec (x#1) (x#3) (x#5))

/-- 不含无序对函数的配对规格只执行奇数区变量重编码。 -/
private theorem formula_pair_spec_point :
    FunctionGraphElimination.formula data
        (pair_spec (x#0) (x#1) (x#2)) =
      pair_spec (x#1) (x#3) (x#5) := by
  rw [formula_eq_source_of_avoids]
  · simp [source_formula, source_term,
      pair_spec, pair_member_condition,
      source_id]
  · simp [pair_spec, pair_member_condition,
      FormulaAvoids, TermsAvoid, TermAvoids]

/-- 开放定义实例的编译只生成一个偶数图见证。 -/
private theorem formula_definition_point :
    FunctionGraphElimination.formula
        data definition_point =
      compiled_definition_point := by
  unfold definition_point
    pair_definition_instance
  rw [FunctionGraphElimination.formula]
  rw [formula_pair_spec_point]
  simp [compiled_definition_point,
    FunctionGraphElimination.formula,
    FunctionGraphElimination.equality,
    FunctionGraphElimination.terms,
    FunctionGraphElimination.term,
    close_witnesses, condition_conjunction,
    data, graph, source_id, witness_id]

/-- 配对存在理论是闭句理论，因而任意证明级 eigenvariable 均对理论新鲜。 -/
private theorem theory_fresh
    (id : FreeVarId) :
    ∀ source, pairing_theory source →
      (SetSort.set, id) ∉
        Formula.freeSupport source := by
  intro source hSource
  rw [(graph_presentation.theory_sentence
    hSource).2]
  exact List.not_mem_nil

/-- 配对存在理论逐点证明编译后的无序对定义公式。 -/
private theorem compiled_definition_point_derives :
    Derives pairing_theory []
      compiled_definition_point := by
  unfold compiled_definition_point
  let arguments : List SetTerm :=
    [x#1, x#3]
  have hArguments :
      ArgsAdmissible arguments
        [SetSort.set, SetSort.set] := by
    exact ArgsAdmissible.cons
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
      Formula.conj
        (pair_spec (x#1) (x#3) (x#0))
        ((x#5) ≐ₘ (x#0))
    apply Derives.exists_elim
        (sort := SetSort.set)
        (eigen := 0)
        (body := body)
    · exact theory_fresh 0
    · intro source hSource
      rcases List.mem_singleton.mp hSource
        with rfl
      simpa [Formula.freeSupport] using
        Formula.not_mem_freeSupport_closeFreeAt
          SetSort.set 0 0 body
    · native_decide
    · simpa [body] using
        (Derives.assumption_of_mem
          (by simp) :
          Derives pairing_theory
            [∃ₘ[SetSort.set, 0], body]
            (∃ₘ[SetSort.set, 0], body))
    · have hBody :
          Derives pairing_theory
            [body,
              ∃ₘ[SetSort.set, 0], body]
            body :=
        Derives.assumption_of_mem
          (by simp)
      have hGraph :=
        Derives.conj_elim_left hBody
      have hEquality :=
        Derives.conj_elim_right hBody
      have hSymmetry :=
        Metatheory.Derives.equality_symm
          hEquality
      have hTransport :=
        graph_presentation.graph_result_congr
          hArguments hZero hFive hSymmetry
      have hResult :=
        Derives.iff_elim_right
          hTransport hGraph
      simpa [body, arguments, graph] using
        hResult
  ·
    let graphBody :=
      pair_spec (x#1) (x#3) (x#0)
    have hExists :
        Derives pairing_theory
          [pair_spec (x#1) (x#3) (x#5)]
          (Formula.existsE SetSort.set
            (Formula.closeFreeAt
              SetSort.set 0 0 graphBody)) := by
      have hBase :=
        graph_presentation.total
          0 hArguments (by
            simp [arguments,
              Term.freeSupportList,
              Term.freeSupport])
      simpa [graph, graphBody, arguments] using
        hBase.context_weaken_cons
    apply graph_presentation.exists_conj_of_case
    · intro source hSource
      rcases List.mem_singleton.mp hSource
        with rfl
      native_decide
    · exact hExists
    · have hWitnessGraph :
          Derives pairing_theory
            [graphBody,
              pair_spec (x#1) (x#3) (x#5)]
            graphBody :=
        Derives.assumption_of_mem
          (by simp)
      have hCandidateGraph :
          Derives pairing_theory
            [graphBody,
              pair_spec (x#1) (x#3) (x#5)]
            (pair_spec
              (x#1) (x#3) (x#5)) :=
        Derives.assumption_of_mem
          (by simp)
      have hFunctional :=
        graph_presentation.functional
          hArguments hFive hZero
      have hFunctional' :
          Derives pairing_theory
            [graphBody,
              pair_spec (x#1) (x#3) (x#5)]
            (Formula.imp
              (pair_spec
                (x#1) (x#3) (x#5))
              (Formula.imp graphBody
                ((x#5) ≐ₘ (x#0)))) := by
        simpa [graphBody, arguments, graph] using
          hFunctional.context_weaken
            (Δ :=
              [graphBody,
                pair_spec
                  (x#1) (x#3) (x#5)])
            (by
              intro source hSource
              cases hSource)
      have hEquality :=
        (hFunctional'.imp_elim
          hCandidateGraph).imp_elim
            hWitnessGraph
      simpa [graphBody, arguments, graph] using
        hEquality

/-- 配对存在理论中的公理不含无序对函数，故编译后严格保持不变。 -/
private theorem formula_base_eq
    {source : SetFormula}
    (hSource : pairing_theory source) :
    FunctionGraphElimination.formula data source =
      source := by
  apply formula_eq_of_sentence_avoids
    data source
  · change
      source = pairing_axiom ∨
        extensionality_theory source at hSource
    rcases hSource with rfl | hSource
    · simpa [pairing_axiom] using
        formula_avoids_forall_close
          FunctionSymbol.unorderedPair
          [(SetSort.set, 0),
            (SetSort.set, 1)]
          (pair_exists (x#0) (x#1)) <| by
            simp [pair_exists, pair_member_condition,
              FormulaAvoids, TermsAvoid,
              TermAvoids]
    · change source = extensionality_axiom
        at hSource
      subst source
      simpa [extensionality_axiom] using
        formula_avoids_forall_close
          FunctionSymbol.unorderedPair
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

/-- 已证明的开放编译公式可沿一个源自由变量闭合。 -/
private theorem formula_forall_close_derives
    (id : FreeVarId) (source : SetFormula)
    (hSource : Formula.Admissible source)
    (hCompiled :
      Derives pairing_theory []
        (FunctionGraphElimination.formula
          data source)) :
    Derives pairing_theory []
      (FunctionGraphElimination.formula data
        (Formula.forallE SetSort.set
          (Formula.closeFreeAt
            SetSort.set id 0 source))) := by
  have hClosed :
      Derives pairing_theory []
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

/-- 配对存在理论证明整个无序对定义公理的函数图编译。 -/
private theorem formula_definition_axiom_derives :
    Derives pairing_theory []
      (FunctionGraphElimination.formula
        data pair_definition_axiom) := by
  have hPoint :
      Derives pairing_theory []
        (FunctionGraphElimination.formula
          data definition_point) := by
    rw [formula_definition_point]
    exact compiled_definition_point_derives
  have hPointAdmissible :
      Formula.Admissible definition_point := by
    exact pair_definition_instance_admissible
      (set_variable_admissible 0)
      (set_variable_admissible 1)
      (set_variable_admissible 2)
  have hCandidate :=
    formula_forall_close_derives
      2 definition_point
      hPointAdmissible hPoint
  have hCandidateAdmissible :
      Formula.Admissible
        (Formula.forallE SetSort.set
          (Formula.closeFreeAt
            SetSort.set 2 0
            definition_point)) :=
    Formula.Admissible.forall_closeFreeAt
      SetSort.set 2 hPointAdmissible
  have hRight :=
    formula_forall_close_derives
      1
      (Formula.forallE SetSort.set
        (Formula.closeFreeAt
          SetSort.set 2 0
          definition_point))
      hCandidateAdmissible hCandidate
  have hRightAdmissible :
      Formula.Admissible
        (Formula.forallE SetSort.set
          (Formula.closeFreeAt
            SetSort.set 1 0
            (Formula.forallE SetSort.set
              (Formula.closeFreeAt
                SetSort.set 2 0
                definition_point)))) :=
    Formula.Admissible.forall_closeFreeAt
      SetSort.set 1 hCandidateAdmissible
  have hLeft :=
    formula_forall_close_derives
      0
      (Formula.forallE SetSort.set
        (Formula.closeFreeAt
          SetSort.set 1 0
          (Formula.forallE SetSort.set
            (Formula.closeFreeAt
              SetSort.set 2 0
              definition_point))))
      hRightAdmissible hRight
  simpa [pair_definition_axiom,
    definition_point] using hLeft

/-- 无序对函数扩张的每条公理均可在配对存在理论中消去函数图。 -/
private theorem compile_axiom
    {source : SetFormula}
    (hSource :
      pairing_operator_theory source) :
    Derives pairing_theory []
      (FunctionGraphElimination.formula
        data source) := by
  rcases hSource with rfl | hSource
  · exact formula_definition_axiom_derives
  · rw [formula_base_eq hSource]
    exact Derives.theory_mem hSource
      (hFormulaCheck :=
        Formula.check_certificate_of_admissible
          (pairing_theory_admissible
            source hSource))

/-- 无序对函数扩张的理论级函数图消去表示。 -/
def theory_presentation :
    TheoryPresentation data where
  graph := graph_presentation
  source := pairing_operator_theory
  compile_axiom := compile_axiom

/-- 无序对函数扩张的 Hilbert 证明可整体翻译到配对存在理论。 -/
theorem hilbert
    {source : SetFormula}
    (hSource :
      HilbertDerives
        pairing_operator_theory source) :
    Derives pairing_theory []
      (FunctionGraphElimination.formula
        data source) :=
  theory_presentation.hilbert hSource

/-- 无序对函数扩张的 checked 自然演绎证明可整体翻译到配对存在理论。 -/
theorem derives
    {source : SetFormula}
    (hSource :
      Derives pairing_operator_theory []
        source) :
    Derives pairing_theory []
      (FunctionGraphElimination.formula
        data source) :=
  theory_presentation.derives
    SetSort.set hSource

/-- 无序对函数扩张中的 Hilbert 矛盾回传为配对存在理论矛盾。 -/
theorem hilbert_falsum
    (hSource :
      HilbertDerives
        pairing_operator_theory
        Formula.falsum) :
    Derives pairing_theory []
      Formula.falsum :=
  theory_presentation.hilbert_falsum hSource

/-- 无序对函数扩张中的 checked 矛盾回传为配对存在理论矛盾。 -/
theorem derives_falsum
    (hSource :
      Derives pairing_operator_theory []
        Formula.falsum) :
    Derives pairing_theory []
      Formula.falsum :=
  theory_presentation.derives_falsum
    SetSort.set hSource

/-- 配对存在理论一致时，无序对函数定义扩张保持 checked 一致。 -/
theorem consistent
    (hBase :
      Derives.Consistent
        pairing_theory []) :
    Derives.Consistent
      pairing_operator_theory [] :=
  theory_presentation.consistent
    SetSort.set hBase

/-- 配对存在理论一致时，无序对函数定义扩张保持 Hilbert 一致。 -/
theorem hilbert_consistent
    (hBase :
      Derives.Consistent
        pairing_theory []) :
    ¬ HilbertDerives
        pairing_operator_theory
        Formula.falsum :=
  theory_presentation.hilbert_consistent hBase

private theorem realizes
    {arguments : List SetTerm}
    (hArguments :
      ArgsAdmissible arguments
        (signature.funcDomain
          FunctionSymbol.unorderedPair)) :
    Derives pairing_operator_theory [] <|
      graph arguments
        (.app FunctionSymbol.unorderedPair
          arguments) := by
  change ArgsAdmissible arguments
    [SetSort.set, SetSort.set] at hArguments
  rcases pair_admissible hArguments with
    ⟨left, right, rfl, hLeft, hRight⟩
  simpa [graph, unordered_pair_term] using
    unordered_pair_term_spec_derives
      left right hLeft hRight

/-- 无序对函数定义扩张的完整函数图表示。 -/
def presentation : DefinitionPresentation data where
  toGraphPresentation := graph_presentation
  extension := pairing_operator_theory
  extension_sentence :=
    pairing_operator_theory_sentence
  base_subset := by
    intro φ hφ
    exact Or.inr hφ
  realizes := realizes

/-- 无序对函数图编译与原闭句在函数扩张中等价。 -/
theorem sentence_iff
    {source : SetFormula}
    (hSource : Formula.Sentence source) :
    Derives pairing_operator_theory []
      (Formula.iff
        (FunctionGraphElimination.formula
          data source)
        source) :=
  presentation.sentence_iff hSource

end UnorderedPair
end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
