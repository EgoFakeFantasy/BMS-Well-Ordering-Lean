import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Hilbert
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.CartesianProduct

/-
# 笛卡尔积函数图消去实例

笛卡尔积由复合母集上的闭分离规格给出。图的全体性消费笛卡尔积分离公理，
单值性消费外延性；函数定义公理的编译只在基理论中重放这两个合同。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace FunctionGraphElimination
namespace CartesianProduct

open Nonlogical.BasicSetTheory
open scoped Symbols

set_option autoImplicit false

/-- 一次增加集合 sort 的 bound scope。 -/
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

private theorem push_push_push_scoped
    {scope : Scope signature} {term : SetTerm}
    (hTerm : TermScoped scope term) :
    TermScoped
      (Scope.push
        (Scope.push (Scope.push scope SetSort.set)
          SetSort.set) SetSort.set) term :=
  push_scoped (push_push_scoped hTerm)

private theorem union_well_sorted
    {left right : SetTerm}
    (hLeft : TermWellSorted left SetSort.set)
    (hRight : TermWellSorted right SetSort.set) :
    TermWellSorted (left ∪ₘ right) SetSort.set := by
  simpa [binary_union_term, signature] using
    (TermWellSorted.app
      (σ := signature) FunctionSymbol.binaryUnion
      (ArgsWellSorted.cons hLeft
        (ArgsWellSorted.cons hRight
          ArgsWellSorted.nil)))

private theorem power_well_sorted
    {source : SetTerm}
    (hSource : TermWellSorted source SetSort.set) :
    TermWellSorted (𝒫ₘ(source)) SetSort.set := by
  simpa [power_set_term, signature] using
    (TermWellSorted.app
      (σ := signature) FunctionSymbol.powerSet
      (ArgsWellSorted.cons hSource ArgsWellSorted.nil))

private theorem bound_well_sorted
    {left right : SetTerm}
    (hLeft : TermWellSorted left SetSort.set)
    (hRight : TermWellSorted right SetSort.set) :
    TermWellSorted
      (cartesian_product_bound_term left right) SetSort.set := by
  exact power_well_sorted
    (power_well_sorted
      (union_well_sorted hLeft hRight))

private theorem pair_well_sorted
    {left right : SetTerm}
    (hLeft : TermWellSorted left SetSort.set)
    (hRight : TermWellSorted right SetSort.set) :
    TermWellSorted (⟨left, right⟩ₘ) SetSort.set := by
  simpa [ordered_pair_term, signature] using
    (TermWellSorted.app
      (σ := signature) FunctionSymbol.orderedPair
      (ArgsWellSorted.cons hLeft
        (ArgsWellSorted.cons hRight ArgsWellSorted.nil)))

private theorem union_scoped
    {scope : Scope signature} {left right : SetTerm}
    (hLeft : TermScoped scope left)
    (hRight : TermScoped scope right) :
    TermScoped scope (left ∪ₘ right) := by
  simpa [binary_union_term] using
    (TermScoped.app
      (σ := signature) (ctx := scope)
      FunctionSymbol.binaryUnion [left, right] (by
        intro term hTerm
        rcases List.mem_cons.mp hTerm with rfl | hTerm
        · exact hLeft
        · rw [List.mem_singleton.mp hTerm]
          exact hRight))

private theorem power_scoped
    {scope : Scope signature} {source : SetTerm}
    (hSource : TermScoped scope source) :
    TermScoped scope (𝒫ₘ(source)) := by
  simpa [power_set_term] using
    (TermScoped.app
      (σ := signature) (ctx := scope)
      FunctionSymbol.powerSet [source] (by
        intro term hTerm
        rw [List.mem_singleton.mp hTerm]
        exact hSource))

private theorem bound_scoped
    {scope : Scope signature} {left right : SetTerm}
    (hLeft : TermScoped scope left)
    (hRight : TermScoped scope right) :
    TermScoped scope
      (cartesian_product_bound_term left right) :=
  power_scoped (power_scoped (union_scoped hLeft hRight))

private theorem pair_scoped
    {scope : Scope signature} {left right : SetTerm}
    (hLeft : TermScoped scope left)
    (hRight : TermScoped scope right) :
    TermScoped scope (⟨left, right⟩ₘ) := by
  simpa [ordered_pair_term] using
    (TermScoped.app
      (σ := signature) (ctx := scope)
      FunctionSymbol.orderedPair [left, right] (by
        intro term hTerm
        rcases List.mem_cons.mp hTerm with rfl | hTerm
        · exact hLeft
        · rw [List.mem_singleton.mp hTerm]
          exact hRight))

/-- 笛卡尔积图；错误元数仅作为不可达外分支落到假。 -/
def graph : List SetTerm → SetTerm → SetFormula
  | (left :: right :: []), product =>
      cartesian_product_spec left right product
  | _, _ =>
      .falsum

private theorem graph_well_formed
    {arguments : List SetTerm} {result : SetTerm}
    (hArguments :
      ArgsWellSorted arguments
        (signature.funcDomain
          FunctionSymbol.cartesianProduct))
    (hResult : TermWellSorted result SetSort.set) :
    FormulaWellFormed (graph arguments result) := by
  change ArgsWellSorted arguments
    [SetSort.set, SetSort.set] at hArguments
  cases hArguments with
  | cons hLeft hTail =>
      cases hTail with
      | cons hRight hNil =>
          cases hNil
          unfold graph cartesian_product_spec
          have hBound :=
            bound_well_sorted hLeft hRight
          apply FormulaWellFormed.forallE
          apply FormulaWellFormed.iff
          · apply FormulaWellFormed.rel
            simpa [signature] using
              ArgsWellSorted.cons
                (TermWellSorted.bvar
                  (σ := signature) SetSort.set 0)
                (ArgsWellSorted.cons hResult
                  ArgsWellSorted.nil)
          · apply FormulaWellFormed.conj
            · apply FormulaWellFormed.rel
              simpa [signature] using
                ArgsWellSorted.cons
                  (TermWellSorted.bvar
                    (σ := signature) SetSort.set 0)
                  (ArgsWellSorted.cons
                    (bound_well_sorted hLeft hRight)
                    ArgsWellSorted.nil)
            · apply FormulaWellFormed.existsE
              apply FormulaWellFormed.existsE
              apply FormulaWellFormed.conj
              · apply FormulaWellFormed.rel
                exact
                  ArgsWellSorted.cons
                    (TermWellSorted.bvar
                      (σ := signature) SetSort.set 1)
                    (ArgsWellSorted.cons hLeft
                      ArgsWellSorted.nil)
              · apply FormulaWellFormed.conj
                · apply FormulaWellFormed.rel
                  exact
                    ArgsWellSorted.cons
                      (TermWellSorted.bvar
                        (σ := signature) SetSort.set 0)
                      (ArgsWellSorted.cons hRight
                        ArgsWellSorted.nil)
                · apply FormulaWellFormed.equal
                  · exact TermWellSorted.bvar
                      (σ := signature) SetSort.set 2
                  · simpa [ordered_pair_term, signature] using
                      (TermWellSorted.app
                        (σ := signature)
                        FunctionSymbol.orderedPair
                        (ArgsWellSorted.cons
                          (TermWellSorted.bvar
                            (σ := signature) SetSort.set 1)
                          (ArgsWellSorted.cons
                            (TermWellSorted.bvar
                              (σ := signature) SetSort.set 0)
                            ArgsWellSorted.nil)))

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
  | cons left tail =>
      cases tail with
      | nil =>
          exact FormulaScoped.falsum
      | cons right rest =>
          cases rest with
          | cons extra rest =>
              exact FormulaScoped.falsum
          | nil =>
              have hLeft := hArguments left (by simp)
              have hRight := hArguments right (by simp)
              have hLeft₃ := push_push_push_scoped hLeft
              have hRight₃ := push_push_push_scoped hRight
              unfold graph cartesian_product_spec
              apply FormulaScoped.forallE
              apply FormulaScoped.iff
              · apply FormulaScoped.rel
                intro term hTerm
                rcases List.mem_cons.mp hTerm with rfl | hTerm
                · exact TermScoped.bvar <| by
                    simp [Scope.push]
                · rw [List.mem_singleton.mp hTerm]
                  exact push_scoped hResult
              · apply FormulaScoped.conj
                · apply FormulaScoped.rel
                  intro term hTerm
                  rcases List.mem_cons.mp hTerm with rfl | hTerm
                  · exact TermScoped.bvar <| by
                      simp [Scope.push]
                  · rw [List.mem_singleton.mp hTerm]
                    exact push_scoped
                      (bound_scoped hLeft hRight)
                · apply FormulaScoped.existsE
                  apply FormulaScoped.existsE
                  apply FormulaScoped.conj
                  · apply FormulaScoped.rel
                    intro term hTerm
                    rcases List.mem_cons.mp hTerm with rfl | hTerm
                    · exact TermScoped.bvar <| by
                        simp [Scope.push]
                    · rw [List.mem_singleton.mp hTerm]
                      exact hLeft₃
                  · apply FormulaScoped.conj
                    · apply FormulaScoped.rel
                      intro term hTerm
                      rcases List.mem_cons.mp hTerm with rfl | hTerm
                      · exact TermScoped.bvar <| by
                          simp [Scope.push]
                      · rw [List.mem_singleton.mp hTerm]
                        exact hRight₃
                    · apply FormulaScoped.equal
                      · exact TermScoped.bvar <| by
                          simp [Scope.push]
                      · exact
                          TermScoped.app
                            (σ := signature) (ctx :=
                              Scope.push
                                (Scope.push
                                  (Scope.push scope SetSort.set)
                                  SetSort.set)
                                SetSort.set)
                            FunctionSymbol.orderedPair
                            [Term.var (.bvar SetSort.set 1),
                              Term.var (.bvar SetSort.set 0)] (by
                              intro term hTerm
                              rcases List.mem_cons.mp hTerm with rfl | hTerm
                              · exact TermScoped.bvar <| by
                                  simp [Scope.push]
                              · rw [List.mem_singleton.mp hTerm]
                                exact TermScoped.bvar <| by
                                  simp [Scope.push])

private theorem graph_freeSupport
    {arguments : List SetTerm} {result : SetTerm}
    {freeVariable : FreeVariable signature}
    (hMember :
      freeVariable ∈ Formula.freeSupport
        (graph arguments result)) :
    freeVariable ∈ Term.freeSupportList arguments ∨
      freeVariable ∈ Term.freeSupport result := by
  cases arguments with
  | nil =>
      simp [graph, Formula.freeSupport] at hMember
  | cons left tail =>
      cases tail with
      | nil =>
          simp [graph, Formula.freeSupport] at hMember
      | cons right rest =>
          cases rest with
          | cons extra rest =>
              simp [graph, Formula.freeSupport] at hMember
          | nil =>
              simpa [graph, cartesian_product_spec,
                cartesian_product_bound_term,
                power_set_binary_union_term,
                Formula.freeSupport,
                Term.freeSupportList,
                Term.freeSupport,
                binary_union_term, power_set_term,
                ordered_pair_term, or_comm,
                or_left_comm, or_assoc] using hMember

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
  | cons left tail =>
      cases tail with
      | nil =>
          rfl
      | cons right rest =>
          cases rest with
          | cons extra rest =>
              rfl
          | nil =>
              cases target
              simp [graph, cartesian_product_spec,
                cartesian_product_bound_term,
                binary_union_term, power_set_term,
                ordered_pair_term,
                Formula.substituteFree,
                Term.substituteFree]

private theorem graph_avoids
    {arguments : List SetTerm} {result : SetTerm}
    (hArguments :
      TermsAvoid FunctionSymbol.cartesianProduct arguments)
    (hResult :
      TermAvoids FunctionSymbol.cartesianProduct result) :
    FormulaAvoids FunctionSymbol.cartesianProduct
      (graph arguments result) := by
  cases arguments with
  | nil =>
      trivial
  | cons left tail =>
      cases tail with
      | nil =>
          trivial
      | cons right rest =>
          cases rest with
          | cons extra rest =>
              trivial
          | nil =>
              simp [graph, cartesian_product_spec,
                cartesian_product_bound_term,
                binary_union_term, power_set_term,
                ordered_pair_term,
                FormulaAvoids, TermsAvoid,
                TermAvoids, hResult,
                hArguments left (by simp),
                hArguments right (by simp)]

/-- 已实现的笛卡尔积函数图消去数据。 -/
def data : Data signature where
  symbol := FunctionSymbol.cartesianProduct
  sort := SetSort.set
  codomain_eq := rfl
  graph := CartesianProduct.graph
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
  rcases hArguments with ⟨hSorted, hScoped⟩
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
          FunctionSymbol.cartesianProduct))
    (hFresh :
      (SetSort.set, resultId) ∉
        Term.freeSupportList arguments) :
    Derives cartesian_product_theory [] <|
      Formula.existsE SetSort.set <|
        Formula.closeFreeAt SetSort.set resultId 0 <|
          graph arguments <|
            .var (.fvar SetSort.set resultId) := by
  change ArgsAdmissible arguments
    [SetSort.set, SetSort.set] at hArguments
  rcases pair_admissible hArguments with
    ⟨left, right, rfl, hLeft, hRight⟩
  have hLeftFresh :
      (SetSort.set, resultId) ∉
        Term.freeSupport left := by
    intro hMember
    exact hFresh
      (Term.mem_freeSupportList_of_mem
        (by simp) hMember)
  have hRightFresh :
      (SetSort.set, resultId) ∉
        Term.freeSupport right := by
    intro hMember
    exact hFresh
      (Term.mem_freeSupportList_of_mem
        (by simp) hMember)
  have hLeftClose₁ :
      Term.closeFreeAt SetSort.set resultId 1 left =
        left :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set resultId 1 left hLeft.2 hLeftFresh
  have hRightClose₁ :
      Term.closeFreeAt SetSort.set resultId 1 right =
        right :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set resultId 1 right hRight.2 hRightFresh
  have hLeftClose₃ :
      Term.closeFreeAt SetSort.set resultId 3 left =
        left :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set resultId 3 left hLeft.2 hLeftFresh
  have hRightClose₃ :
      Term.closeFreeAt SetSort.set resultId 3 right =
        right :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set resultId 3 right hRight.2 hRightFresh
  simpa [graph, cartesian_product_exists,
    cartesian_product_spec,
    cartesian_product_bound_term,
    binary_union_term, power_set_term,
    ordered_pair_term,
    Formula.closeFreeAt, Formula.next_depth,
    Term.closeFreeAt, hLeftClose₁,
    hRightClose₁, hLeftClose₃,
    hRightClose₃] using
    cartesian_product_exists_derives left right
      hLeft hRight

private theorem functional
    {arguments : List SetTerm}
    {left right : SetTerm}
    (hArguments :
      ArgsAdmissible arguments
        (signature.funcDomain
          FunctionSymbol.cartesianProduct))
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    Derives cartesian_product_theory [] <|
      Formula.imp (graph arguments left) <|
        Formula.imp (graph arguments right) <|
          Formula.equal left right := by
  change ArgsAdmissible arguments
    [SetSort.set, SetSort.set] at hArguments
  rcases pair_admissible hArguments with
    ⟨first, second, rfl, hFirst, hSecond⟩
  have hSpecLeft :
      Formula.Admissible
        (cartesian_product_spec first second left) :=
    cartesian_product_spec_admissible
      hFirst hSecond hLeft
  have hSpecRight :
      Formula.Admissible
        (cartesian_product_spec first second right) :=
    cartesian_product_spec_admissible
      hFirst hSecond hRight
  have hUniqueBase :
      Derives extensionality_theory []
        (cartesian_product_spec first second left ⟶ₘ
          (cartesian_product_spec first second right ⟶ₘ
            (left ≐ₘ right))) := by
    simpa [cartesian_product_spec,
      cartesian_product_member_condition,
      cartesian_product_bound_term,
      binary_union_term, power_set_term,
      ordered_pair_term] using
      (membership_specification_unique
        left right
        ((bₛ#0 ∈ₘ
          cartesian_product_bound_term first second) ∧ₘ
          (∃ₘ[SetSort.set],
            ∃ₘ[SetSort.set],
              (bₛ#1 ∈ₘ first) ∧ₘ
                ((bₛ#0 ∈ₘ second) ∧ₘ
                  (bₛ#2 ≐ₘ
                    ⟨bₛ#1, bₛ#0⟩ₘ))))
        hLeft hRight hSpecLeft hSpecRight)
  have hUnique :
      Derives cartesian_product_theory []
        (cartesian_product_spec first second left ⟶ₘ
          (cartesian_product_spec first second right ⟶ₘ
            (left ≐ₘ right))) :=
    Derives.theory_weaken
      (fun _ hφ =>
        cartesian_product_base_theory_subset_cartesian_product_theory <|
          extensionality_theory_subset_cartesian_product_base_theory
            hφ)
      hUniqueBase
  apply Derives.impIntro
    (hAntecedentCheck :=
      Formula.check_certificate_of_admissible
        (graph_admissible data
          (ArgsAdmissible.cons hFirst
            (ArgsAdmissible.cons hSecond
              ArgsAdmissible.nil)) hLeft))
  apply Derives.impIntro
    (hAntecedentCheck :=
      Formula.check_certificate_of_admissible
        (graph_admissible data
          (ArgsAdmissible.cons hFirst
            (ArgsAdmissible.cons hSecond
              ArgsAdmissible.nil)) hRight))
  have hLeftGraph :
      Derives cartesian_product_theory
        [graph [first, second] right,
          graph [first, second] left]
        (cartesian_product_spec first second left) := by
    simpa [graph] using
      (Derives.assumption_of_mem (by simp) :
        Derives cartesian_product_theory
          [graph [first, second] right,
            graph [first, second] left]
          (graph [first, second] left))
  have hRightGraph :
      Derives cartesian_product_theory
        [graph [first, second] right,
          graph [first, second] left]
        (cartesian_product_spec first second right) := by
    simpa [graph] using
      (Derives.assumption_of_mem (by simp) :
        Derives cartesian_product_theory
          [graph [first, second] right,
            graph [first, second] left]
          (graph [first, second] right))
  exact Derives.impElim
    (Derives.impElim
      (hUnique.context_weaken (by simp))
      hLeftGraph)
    hRightGraph

/-- 笛卡尔积理论给出的全体、单值函数图表示。 -/
def graph_presentation : GraphPresentation data where
  theory := cartesian_product_theory
  theory_sentence := cartesian_product_theory_sentence
  total := total
  functional := functional

private def definition_point : SetFormula :=
  cartesian_product_definition_instance
    (x#0) (x#1) (x#2)

private def compiled_definition_point : SetFormula :=
  (∃ₘ[SetSort.set, 0],
      graph [x#1, x#3] (x#0) ∧ₘ
        ((x#5) ≐ₘ (x#0))) ↔ₘ
    cartesian_product_spec
      (x#1) (x#3) (x#5)

private theorem formula_spec_point :
    FunctionGraphElimination.formula data
        (cartesian_product_spec
          (x#0) (x#1) (x#2)) =
      cartesian_product_spec
        (x#1) (x#3) (x#5) := by
  rw [formula_eq_source_of_avoids]
  · simp [cartesian_product_spec,
      cartesian_product_bound_term,
      binary_union_term, power_set_term,
      ordered_pair_term, source_formula,
      source_term, source_id]
  · apply checkFormulaAvoids_sound
    native_decide

private theorem formula_definition_point :
    FunctionGraphElimination.formula data
        definition_point =
      compiled_definition_point := by
  unfold definition_point
    cartesian_product_definition_instance
  rw [FunctionGraphElimination.formula]
  rw [formula_spec_point]
  simp [compiled_definition_point,
    FunctionGraphElimination.formula,
    FunctionGraphElimination.equality,
    FunctionGraphElimination.terms,
    FunctionGraphElimination.term,
    close_witnesses, condition_conjunction,
    data, graph, source_id, witness_id,
    cartesian_product_term]

private theorem formula_base_eq
    {source : SetFormula}
    (hSource : cartesian_product_theory source) :
    FunctionGraphElimination.formula data source = source := by
  apply formula_eq_of_sentence_avoids data source
  · apply checkFormulaAvoids_sound
    simp only [cartesian_product_theory,
      cartesian_product_base_theory,
      Theory.insert, Theory.union] at hSource
    repeat'
      first
      | obtain hSource | hSource := hSource
      | subst source
    all_goals native_decide
  · exact cartesian_product_theory_sentence hSource

private theorem theory_fresh
    (id : FreeVarId) :
    ∀ source, cartesian_product_theory source →
      (SetSort.set, id) ∉ Formula.freeSupport source := by
  intro source hSource
  rw [(cartesian_product_theory_sentence hSource).2]
  exact List.not_mem_nil

private theorem compiled_definition_point_derives :
    Derives cartesian_product_theory []
      compiled_definition_point := by
  unfold compiled_definition_point
  let witnessBody : SetFormula :=
    graph [x#1, x#3] (x#0) ∧ₘ
      ((x#5) ≐ₘ (x#0))
  let witnessExists : SetFormula :=
    ∃ₘ[SetSort.set, 0], witnessBody
  apply Derives.iff_intro
  ·
    let Γ₀ : Context signature := [witnessExists]
    let Γ : Context signature := witnessBody :: Γ₀
    have hExists :
        Derives cartesian_product_theory Γ₀
          witnessExists :=
      Derives.assumption_of_mem (by simp [Γ₀])
    have hBody :
        Derives cartesian_product_theory Γ witnessBody :=
      Derives.assumption_of_mem (by simp [Γ])
    have hGraph :
        Derives cartesian_product_theory Γ
          (cartesian_product_spec (x#1) (x#3) (x#0)) := by
      simpa [witnessBody, graph] using
        Derives.conj_elim_left hBody
    have hEquality :
        Derives cartesian_product_theory Γ
          ((x#5) ≐ₘ (x#0)) :=
      Derives.conj_elim_right hBody
    have hBodyCheck :
        Formula.CheckCertificate
          (cartesian_product_spec
            (x#1) (x#3) (x#7)) :=
      Formula.check_certificate_of_admissible
        (cartesian_product_spec_admissible
          (set_variable_admissible 1)
          (set_variable_admissible 3)
          (set_variable_admissible 7))
    have hIff :
        Derives cartesian_product_theory Γ
          (cartesian_product_spec
              (x#1) (x#3) (x#5) ↔ₘ
            cartesian_product_spec
              (x#1) (x#3) (x#0)) := by
      have hRaw :=
        Metatheory.Derives.equality_iff_of_equality
          (eigen := 7)
          hEquality
          (hLeftCheck :=
            Term.check_certificate_of_admissible
              (set_variable_admissible 5))
          (hRightCheck :=
            Term.check_certificate_of_admissible
              (set_variable_admissible 0))
          (hBodyCheck := hBodyCheck)
      simpa [cartesian_product_spec,
        cartesian_product_bound_term,
        binary_union_term, power_set_term,
        ordered_pair_term,
        Formula.substituteFree,
        Term.substituteFree] using hRaw
    have hSpec :
        Derives cartesian_product_theory Γ
          (cartesian_product_spec
            (x#1) (x#3) (x#5)) :=
      Derives.iffElimLeft hIff hGraph
    exact Derives.exists_elim
      (sort := SetSort.set)
      (eigen := 0)
      (body := witnessBody)
      (conclusion :=
        cartesian_product_spec (x#1) (x#3) (x#5))
      (by
        intro φ hφ
        rw [(cartesian_product_theory_sentence hφ).2]
        simp)
      (by
        intro φ hφ
        rcases List.mem_singleton.mp hφ with rfl
        native_decide)
      (by native_decide)
      hExists
      hSpec
  ·
    let Γ : Context signature :=
      [cartesian_product_spec (x#1) (x#3) (x#5)]
    have hSpec :
        Derives cartesian_product_theory Γ
          (cartesian_product_spec
            (x#1) (x#3) (x#5)) :=
      Derives.assumption_of_mem (by simp [Γ])
    have hGraph :
        Derives cartesian_product_theory Γ
          (graph [x#1, x#3] (x#5)) := by
      unfold graph
      exact hSpec
    have hConj :
        Derives cartesian_product_theory Γ
          (graph [x#1, x#3] (x#5) ∧ₘ
            ((x#5) ≐ₘ (x#5))) :=
      Derives.conj_intro hGraph <|
        Derives.eq_refl_m
          (T := cartesian_product_theory)
          (Γ := Γ) (x#5)
    apply Derives.exists_intro_substituted
      (eigen := 0) (witness := x#5)
    simpa [witnessBody, graph,
      cartesian_product_spec,
      cartesian_product_bound_term,
      binary_union_term, power_set_term,
      ordered_pair_term,
      Formula.substituteFree, Term.substituteFree] using
      hConj

private theorem formula_definition_axiom_derives :
    Derives cartesian_product_theory []
      (FunctionGraphElimination.formula data
        cartesian_product_definition_axiom) := by
  have hPoint :
      Derives cartesian_product_theory []
        (FunctionGraphElimination.formula data
          definition_point) := by
    rw [formula_definition_point]
    exact compiled_definition_point_derives
  have hPointAdmissible :
      Formula.Admissible definition_point :=
    cartesian_product_definition_instance_admissible
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
          (Formula.closeFreeAt SetSort.set
            1 0
            (Formula.forallE SetSort.set
              (Formula.closeFreeAt SetSort.set
                2 0 definition_point)))) :=
    Formula.Admissible.forall_closeFreeAt
      SetSort.set 1 hCandidateAdmissible
  have hLeft :=
    graph_presentation.formula_forall_close_derives
      SetSort.set 0
      (Formula.forallE SetSort.set
        (Formula.closeFreeAt SetSort.set
          1 0
          (Formula.forallE SetSort.set
            (Formula.closeFreeAt SetSort.set
              2 0 definition_point))))
      hRightAdmissible hRight
  simpa [cartesian_product_definition_axiom,
    definition_point] using hLeft

private theorem compile_axiom
    {source : SetFormula}
    (hSource : cartesian_product_operator_theory source) :
    Derives cartesian_product_theory []
      (FunctionGraphElimination.formula data source) := by
  rcases hSource with rfl | hSource
  · exact formula_definition_axiom_derives
  · rw [formula_base_eq hSource]
    exact Derives.theory_mem hSource
      (hFormulaCheck :=
        Formula.check_certificate_of_admissible
          (cartesian_product_theory_admissible
            source hSource))

/-- 笛卡尔积定义扩张的理论级函数图表示。 -/
def theory_presentation : TheoryPresentation data where
  graph := graph_presentation
  source := cartesian_product_operator_theory
  compile_axiom := compile_axiom

theorem hilbert
    {source : SetFormula}
    (hSource :
      HilbertDerives cartesian_product_operator_theory source) :
    Derives cartesian_product_theory []
      (FunctionGraphElimination.formula data source) :=
  theory_presentation.hilbert hSource

theorem derives
    {source : SetFormula}
    (hSource :
      Derives cartesian_product_operator_theory [] source) :
    Derives cartesian_product_theory []
      (FunctionGraphElimination.formula data source) :=
  theory_presentation.derives SetSort.set hSource

theorem hilbert_falsum
    (hSource :
      HilbertDerives cartesian_product_operator_theory
        Formula.falsum) :
    Derives cartesian_product_theory []
      Formula.falsum :=
  theory_presentation.hilbert_falsum hSource

theorem derives_falsum
    (hSource :
      Derives cartesian_product_operator_theory []
        Formula.falsum) :
    Derives cartesian_product_theory []
      Formula.falsum :=
  theory_presentation.derives_falsum
    SetSort.set hSource

theorem consistent
    (hBase :
      Derives.Consistent cartesian_product_theory []) :
    Derives.Consistent cartesian_product_operator_theory [] :=
  theory_presentation.consistent SetSort.set hBase

theorem hilbert_consistent
    (hBase :
      Derives.Consistent cartesian_product_theory []) :
    ¬ HilbertDerives cartesian_product_operator_theory
        Formula.falsum :=
  theory_presentation.hilbert_consistent hBase

private theorem realizes
    {arguments : List SetTerm}
    (hArguments :
      ArgsAdmissible arguments
        (signature.funcDomain
          FunctionSymbol.cartesianProduct)) :
    Derives cartesian_product_operator_theory [] <|
      graph arguments
        (.app FunctionSymbol.cartesianProduct arguments) := by
  change ArgsAdmissible arguments
    [SetSort.set, SetSort.set] at hArguments
  rcases pair_admissible hArguments with
    ⟨left, right, rfl, hLeft, hRight⟩
  simpa [graph, cartesian_product_term] using
    cartesian_product_term_spec_derives
      left right hLeft hRight

def presentation : DefinitionPresentation data where
  toGraphPresentation := graph_presentation
  extension := cartesian_product_operator_theory
  extension_sentence := cartesian_product_operator_theory_sentence
  base_subset := by
    intro φ hφ
    exact Or.inr hφ
  realizes := realizes

theorem sentence_iff
    {source : SetFormula}
    (hSource : Formula.Sentence source) :
    Derives cartesian_product_operator_theory []
      (Formula.iff
        (FunctionGraphElimination.formula data source)
        source) :=
  presentation.sentence_iff hSource

end CartesianProduct
end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
