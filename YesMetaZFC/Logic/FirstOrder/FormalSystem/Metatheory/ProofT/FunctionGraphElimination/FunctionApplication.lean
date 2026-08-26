import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Hilbert
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Function

/-!
# 函数求值图消去实例

对象语言的函数求值只在“输入是函数且参数属于定义域”的 guard 下由函数图规定。
为了把这个偏定义合同提升为函数图编译器要求的全体、单值图，本模块在 guard 外
规范地令结果等于函数参数自身。该回退不引入空集、选择函数或更强背景理论。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace FunctionGraphElimination
namespace FunctionApplication

open Nonlogical.BasicSetTheory
open scoped Symbols

set_option autoImplicit false

/-- 函数求值公理实际约束函数值的自然 guard。 -/
def guard (function argument : SetTerm) : SetFormula :=
  is_function_formula function ∧ₘ
    (argument ∈ₘ domₘ(function))

/--
函数求值的全体化图。guard 内要求候选值属于原函数图；guard 外规范回退到函数
参数自身。两个蕴含同时保留，使定义公理的编译可以直接消费 guard 内分支。
-/
def graph : List SetTerm → SetTerm → SetFormula
  | (function :: argument :: []), result =>
      (guard function argument ⟶ₘ
        (⟨argument, result⟩ₘ ∈ₘ function)) ∧ₘ
      ((¬ₘ guard function argument) ⟶ₘ
        (result ≐ₘ function))
  | _, _ =>
      .falsum

private theorem domain_well_sorted
    {function : SetTerm}
    (hFunction :
      TermWellSorted function SetSort.set) :
    TermWellSorted (domₘ(function)) SetSort.set := by
  simpa [domain_term, signature] using
    (TermWellSorted.app
      (σ := signature) FunctionSymbol.domain
      (ArgsWellSorted.cons hFunction
        ArgsWellSorted.nil))

private theorem pair_well_sorted
    {left right : SetTerm}
    (hLeft : TermWellSorted left SetSort.set)
    (hRight : TermWellSorted right SetSort.set) :
    TermWellSorted (⟨left, right⟩ₘ) SetSort.set := by
  simpa [ordered_pair_term, signature] using
    (TermWellSorted.app
      (σ := signature) FunctionSymbol.orderedPair
      (ArgsWellSorted.cons hLeft
        (ArgsWellSorted.cons hRight
          ArgsWellSorted.nil)))

private theorem graph_well_formed
    {arguments : List SetTerm} {result : SetTerm}
    (hArguments :
      ArgsWellSorted arguments
        (signature.funcDomain FunctionSymbol.application))
    (hResult :
      TermWellSorted result SetSort.set) :
    FormulaWellFormed (graph arguments result) := by
  change ArgsWellSorted arguments
    [SetSort.set, SetSort.set] at hArguments
  cases arguments with
  | nil =>
      cases hArguments
  | cons function tail =>
      cases tail with
      | nil =>
          cases hArguments with
          | cons hFunction hTail =>
              cases hTail
      | cons argument rest =>
          cases rest with
          | cons extra rest =>
              cases hArguments with
              | cons hFunction hTail =>
                  cases hTail with
                  | cons hArgument hRest =>
                      cases hRest
          | nil =>
            rcases hArguments with
              ⟨⟩
            rename_i hFunction hTail
            rcases hTail with ⟨⟩
            rename_i hArgument hNil
            cases hNil
            have hDomain :=
              domain_well_sorted hFunction
            have hPair :=
              pair_well_sorted hArgument hResult
            have hGuard :
                FormulaWellFormed
                  (guard function argument) := by
              apply FormulaWellFormed.conj
              · apply FormulaWellFormed.rel
                simpa [signature] using
                  ArgsWellSorted.cons hFunction
                    ArgsWellSorted.nil
              · apply FormulaWellFormed.rel
                simpa [signature] using
                  ArgsWellSorted.cons hArgument
                    (ArgsWellSorted.cons hDomain
                      ArgsWellSorted.nil)
            apply FormulaWellFormed.conj
            · apply FormulaWellFormed.imp hGuard
              apply FormulaWellFormed.rel
              simpa [signature] using
                ArgsWellSorted.cons hPair
                  (ArgsWellSorted.cons hFunction
                    ArgsWellSorted.nil)
            · exact FormulaWellFormed.imp
                (FormulaWellFormed.neg hGuard)
                (FormulaWellFormed.equal hResult
                  hFunction)

private theorem domain_scoped
    {scope : Scope signature} {function : SetTerm}
    (hFunction : TermScoped scope function) :
    TermScoped scope (domₘ(function)) := by
  simpa [domain_term] using
    (TermScoped.app
      (σ := signature) (ctx := scope)
      FunctionSymbol.domain [function] (by
        intro term hTerm
        rw [List.mem_singleton.mp hTerm]
        exact hFunction))

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
        rcases List.mem_cons.mp hTerm with
          rfl | hTerm
        · exact hLeft
        · rw [List.mem_singleton.mp hTerm]
          exact hRight))

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
  | cons function tail =>
      cases tail with
      | nil =>
          simpa [graph] using
            (FormulaScoped.falsum :
              FormulaScoped scope
                (Formula.falsum : SetFormula))
      | cons argument rest =>
          cases rest with
          | nil =>
              have hFunction :=
                hArguments function (by simp)
              have hArgument :=
                hArguments argument (by simp)
              have hDomain :=
                domain_scoped hFunction
              have hPair :=
                pair_scoped hArgument hResult
              have hGuard :
                  FormulaScoped scope
                    (guard function argument) := by
                apply FormulaScoped.conj
                · apply FormulaScoped.rel
                  intro term hTerm
                  rw [List.mem_singleton.mp hTerm]
                  exact hFunction
                · apply FormulaScoped.rel
                  intro term hTerm
                  rcases List.mem_cons.mp hTerm with
                    rfl | hTerm
                  · exact hArgument
                  · rw [List.mem_singleton.mp hTerm]
                    exact hDomain
              apply FormulaScoped.conj
              · apply FormulaScoped.imp hGuard
                apply FormulaScoped.rel
                intro term hTerm
                rcases List.mem_cons.mp hTerm with
                  rfl | hTerm
                · exact hPair
                · rw [List.mem_singleton.mp hTerm]
                  exact hFunction
              · exact FormulaScoped.imp
                  (FormulaScoped.neg hGuard)
                  (FormulaScoped.equal hResult
                    hFunction)
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
        Formula.freeSupport (graph arguments result)) :
    freeVariable ∈ Term.freeSupportList arguments ∨
      freeVariable ∈ Term.freeSupport result := by
  cases arguments with
  | nil =>
      simp [graph, Formula.freeSupport] at hMember
  | cons function tail =>
      cases tail with
      | nil =>
          simp [graph, Formula.freeSupport] at hMember
      | cons argument rest =>
          cases rest with
          | nil =>
              simpa [graph, guard, domain_term,
                ordered_pair_term,
                Formula.freeSupport,
                Term.freeSupport,
                Term.freeSupportList,
                or_left_comm, or_comm, or_assoc] using
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
  | cons function tail =>
      cases tail with
      | nil =>
          simp [graph, Formula.substituteFree]
      | cons argument rest =>
          cases rest with
          | nil =>
              cases target
              simp [graph, guard, domain_term,
                ordered_pair_term,
                Formula.substituteFree,
                Term.substituteFree]
          | cons extra rest =>
              simp [graph, Formula.substituteFree]

private theorem graph_avoids
    {arguments : List SetTerm} {result : SetTerm}
    (hArguments :
      TermsAvoid FunctionSymbol.application arguments)
    (hResult :
      TermAvoids FunctionSymbol.application result) :
    FormulaAvoids FunctionSymbol.application
      (graph arguments result) := by
  cases arguments with
  | nil =>
      simp [graph, FormulaAvoids]
  | cons function tail =>
      cases tail with
      | nil =>
          simp [graph, FormulaAvoids]
      | cons argument rest =>
          cases rest with
          | nil =>
              have hFunction :=
                hArguments function (by simp)
              have hArgument :=
                hArguments argument (by simp)
              simp [graph, guard, domain_term,
                ordered_pair_term,
                FormulaAvoids, TermsAvoid, TermAvoids,
                hFunction, hArgument, hResult]
          | cons extra rest =>
              simp [graph, FormulaAvoids]

/-- 已实现的函数求值图消去数据。 -/
def data : Data signature where
  symbol := FunctionSymbol.application
  sort := SetSort.set
  codomain_eq := rfl
  graph := FunctionApplication.graph
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
    ∃ function argument,
      arguments = [function, argument] ∧
        Term.Admissible function SetSort.set ∧
        Term.Admissible argument SetSort.set := by
  rcases hArguments with ⟨hSorted, hScoped⟩
  cases hSorted with
  | cons hFunction hTail =>
      cases hTail with
      | cons hArgument hNil =>
          cases hNil
          exact ⟨_, _, rfl,
            ⟨hFunction, hScoped _ (by simp)⟩,
            ⟨hArgument, hScoped _ (by simp)⟩⟩

/--
guard 内的定义域成员确实具有一个函数图值。证明从定义域的关系成员见证出发，
先把该成员重构成自身投影组成的有序对，再沿第一投影等式运输为规范图成员。
-/
theorem guard_graph_value_exists
    (function argument : SetTerm)
    (hFunction :
      Term.Admissible function SetSort.set)
    (hArgument :
      Term.Admissible argument SetSort.set) :
    Derives function_predicate_theory [] <|
      Formula.imp (guard function argument) <|
        Formula.existsE SetSort.set <|
          ⟨argument, bₛ#0⟩ₘ ∈ₘ function := by
  let predicate := guard function argument
  let conclusion : SetFormula :=
    Formula.existsE SetSort.set <|
      ⟨argument, bₛ#0⟩ₘ ∈ₘ function
  let Γ : Context signature := [predicate]
  have hPredicate :
      Formula.Admissible predicate := by
    dsimp [predicate, guard]
    exact Formula.Admissible.conj
      (is_function_formula_admissible hFunction)
      (membership_formula_admissible hArgument
        (domain_term_admissible function hFunction))
  apply Derives.imp_intro
    (hAntecedentCheck :=
      Formula.check_certificate_of_admissible
        hPredicate)
  have hGuard :
      Derives function_predicate_theory Γ
        (guard function argument) := by
    exact Derives.assumption_of_mem
      (by simp [Γ, predicate])
  have hFunctionFormula :
      Derives function_predicate_theory Γ
        (is_function_formula function) :=
    Derives.conj_elim_left hGuard
  have hDomainMember :
      Derives function_predicate_theory Γ
        (argument ∈ₘ domₘ(function)) :=
    Derives.conj_elim_right hGuard
  have hRelation :
      Derives function_predicate_theory Γ
        (is_relation_formula function) := by
    exact Derives.imp_elim
      ((is_function_implies_is_relation
        function hFunction).context_weaken_cons)
      hFunctionFormula
  have hDomainIff :
      Derives function_predicate_theory Γ
        ((argument ∈ₘ domₘ(function)) ↔ₘ
          ((argument ∈ₘ double_union_term function) ∧ₘ
            relation_domain_member_condition
              function argument)) := by
    have hBase :=
      is_relation_domain_member_iff
        function argument hFunction hArgument
    have hLifted :=
      Derives.theory_weaken
        (fun _ hφ =>
          relation_domain_operator_theory_subset_function_predicate_theory
            hφ)
        hBase
    exact Derives.imp_elim
      hLifted.context_weaken_cons hRelation
  have hDescription :=
    Derives.iff_elim_right
      hDomainIff hDomainMember
  have hCoordinateWitness :
      Derives function_predicate_theory Γ
        (relation_domain_member_condition
          function argument) :=
    Derives.conj_elim_right hDescription
  let member :=
    FreshVariable.fresh_id SetSort.set
      [predicate, conclusion]
  let body : SetFormula :=
    (x#member ∈ₘ function) ∧ₘ
      (argument ≐ₘ (x#member)₀ₘ)
  have hMemberFreshPredicate :
      (SetSort.set, member) ∉
        Formula.freeSupport predicate := by
    dsimp [member]
    exact FreshVariable.fresh_id_not_mem_m
      (by simp)
  have hMemberFreshConclusion :
      (SetSort.set, member) ∉
        Formula.freeSupport conclusion := by
    dsimp [member]
    exact FreshVariable.fresh_id_not_mem_m
      (by simp)
  have hMemberFreshFunction :
      (SetSort.set, member) ∉
        Term.freeSupport function := by
    intro hMember
    apply hMemberFreshPredicate
    simp only [predicate, guard,
      Formula.freeSupport, domain_term,
      Term.freeSupport, Term.freeSupportList]
    exact List.mem_append_left _ <| by
      simpa using
        List.mem_append_left [] hMember
  have hMemberFreshArgument :
      (SetSort.set, member) ∉
        Term.freeSupport argument := by
    intro hMember
    apply hMemberFreshPredicate
    simp only [predicate, guard,
      Formula.freeSupport, domain_term,
      Term.freeSupport, Term.freeSupportList]
    exact List.mem_append_right _ <|
      List.mem_append_left _ hMember
  have hExists :
      Derives function_predicate_theory Γ
        (Formula.existsE SetSort.set
          (Formula.closeFreeAt SetSort.set
            member 0 body)) := by
    have hFunctionClose :
        Term.closeFreeAt SetSort.set member 0 function =
          function :=
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
        SetSort.set member 0 function
          hFunction.2 hMemberFreshFunction
    have hArgumentClose :
        Term.closeFreeAt SetSort.set member 0 argument =
          argument :=
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
        SetSort.set member 0 argument
          hArgument.2 hMemberFreshArgument
    simpa [body, relation_domain_member_condition,
      relation_coordinate_member_condition,
      relation_coordinate_projection_term,
      Formula.closeFreeAt, Formula.next_depth,
      Term.closeFreeAt, left_projection_term,
      hFunctionClose, hArgumentClose] using
      hCoordinateWitness
  have hBody :
      Formula.Admissible body := by
    dsimp [body]
    exact Formula.Admissible.conj
      (membership_formula_admissible
        (set_variable_admissible member) hFunction)
      (Formula.Admissible.equal hArgument
        (left_projection_term_admissible
          (x#member)
          (set_variable_admissible member)))
  have hCase :
      Derives function_predicate_theory
        (body :: Γ) conclusion := by
    let candidate := x#member
    let value := (candidate)₁ₘ
    let represented := ⟨argument, value⟩ₘ
    have hCandidate :
        Term.Admissible candidate SetSort.set :=
      set_variable_admissible member
    have hValue :
        Term.Admissible value SetSort.set :=
      right_projection_term_admissible
        candidate hCandidate
    have hRepresented :
        Term.Admissible represented SetSort.set :=
      ordered_pair_term_admissible
        argument value hArgument hValue
    have hBodyProof :
        Derives function_predicate_theory
          (body :: Γ) body :=
      Derives.assumption_of_mem (by simp)
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible
            hBody)
    have hMembership :
        Derives function_predicate_theory
          (body :: Γ)
          (candidate ∈ₘ function) := by
      simpa [body, candidate] using
        Derives.conj_elim_left hBodyProof
    have hLeftEquality :
        Derives function_predicate_theory
          (body :: Γ)
          (argument ≐ₘ (candidate)₀ₘ) := by
      simpa [body, candidate] using
        Derives.conj_elim_right hBodyProof
    have hRelation' :
        Derives function_predicate_theory
          (body :: Γ)
          (is_relation_formula function) :=
      hRelation.context_weaken_cons
    have hOrdered :
        Derives function_predicate_theory
          (body :: Γ)
          (is_ordered_pair_formula candidate) := by
      have hBase :=
        is_relation_member_is_ordered_pair
          function candidate hFunction hCandidate
      have hLifted :=
        Derives.theory_weaken
          (fun _ hφ =>
            relation_plane_theory_subset_function_predicate_theory <|
              relation_predicate_theory_subset_relation_plane_theory
                hφ)
          hBase
      exact Derives.imp_elim
        (Derives.imp_elim
          (hLifted.context_weaken
            (by simp [Γ]))
          hRelation')
        hMembership
    have hReconstruction :
        Derives function_predicate_theory
          (body :: Γ)
          (candidate ≐ₘ
            ⟨(candidate)₀ₘ, value⟩ₘ) := by
      have hBase :=
        is_ordered_pair_eq_ordered_pair_projections
          candidate hCandidate
      have hLifted :=
        Derives.theory_weaken
          (fun _ hφ =>
            relation_plane_theory_subset_function_predicate_theory <|
              ordered_pair_reverse_operator_theory_subset_relation_plane_theory <|
                right_projection_operator_theory_subset_ordered_pair_reverse_operator_theory
                  hφ)
          hBase
      simpa [value] using
        Derives.imp_elim
          (hLifted.context_weaken
            (by simp [Γ]))
          hOrdered
    have hLeftSymmetry :
        Derives function_predicate_theory
          (body :: Γ)
          ((candidate)₀ₘ ≐ₘ argument) :=
      Metatheory.Derives.equality_symm
        hLeftEquality
    have hPairEquality :
        Derives function_predicate_theory
          (body :: Γ)
          (⟨(candidate)₀ₘ, value⟩ₘ ≐ₘ
            represented) := by
      exact
        Metatheory.Derives.binary_term_constructor_congr_of_equalities
          ordered_pair_term
          ordered_pair_term_admissible
          (by
            intros
            simp [Term.substituteFree])
          (candidate)₀ₘ argument value value
          (left_projection_term_admissible
            candidate hCandidate)
          hArgument hValue hValue
          hLeftSymmetry
          (Derives.eq_refl_m
            (T := function_predicate_theory)
            (Γ := body :: Γ)
            value (sort := SetSort.set)
            (hTermCheck :=
              Term.check_certificate_of_admissible
                hValue))
    have hCandidateEquality :
        Derives function_predicate_theory
          (body :: Γ)
          (candidate ≐ₘ represented) :=
      Metatheory.Derives.equality_trans
        hReconstruction hPairEquality
    have hMembershipIff :=
      membership_left_iff_of_equality
        candidate represented function
        hCandidate hRepresented hFunction
        hCandidateEquality
    have hRepresentedMembership :
        Derives function_predicate_theory
          (body :: Γ)
          (represented ∈ₘ function) :=
      Derives.iff_elim_right
        hMembershipIff hMembership
    unfold conclusion
    nd_apply Derives.exists_intro
      (term := value)
    have hArgumentOpen :
        Term.openAt SetSort.set 0 value argument =
          argument :=
      Term.openAt_eq_self_of_boundClosed
        SetSort.set 0 value argument hArgument.2
    have hFunctionOpen :
        Term.openAt SetSort.set 0 value function =
          function :=
      Term.openAt_eq_self_of_boundClosed
        SetSort.set 0 value function hFunction.2
    simpa [represented, value,
      Formula.openAt, Term.openAt,
      ordered_pair_term,
      hArgumentOpen, hFunctionOpen] using
      hRepresentedMembership
  exact Derives.exists_elim
    (by
      intro φ hφ
      rw [(function_predicate_theory_sentence hφ).2]
      simp)
    (by
      intro φ hφ
      rcases List.mem_singleton.mp hφ with rfl
      exact hMemberFreshPredicate)
    hMemberFreshConclusion
    hExists hCase

private theorem total
    {arguments : List SetTerm}
    (resultId : FreeVarId)
    (hArguments :
      ArgsAdmissible arguments
        (signature.funcDomain FunctionSymbol.application))
    (hFresh :
      (SetSort.set, resultId) ∉
        Term.freeSupportList arguments) :
    Derives mapping_predicate_theory [] <|
      Formula.existsE SetSort.set <|
        Formula.closeFreeAt SetSort.set resultId 0 <|
          graph arguments <|
            .var (.fvar SetSort.set resultId) := by
  change ArgsAdmissible arguments
    [SetSort.set, SetSort.set] at hArguments
  rcases pair_admissible hArguments with
    ⟨function, argument, rfl,
      hFunction, hArgument⟩
  let predicate := guard function argument
  let body : SetFormula :=
    graph [function, argument] (x#resultId)
  let conclusion : SetFormula :=
    Formula.existsE SetSort.set <|
      Formula.closeFreeAt SetSort.set resultId 0 body
  have hFunctionFresh :
      (SetSort.set, resultId) ∉
        Term.freeSupport function := by
    intro hMember
    exact hFresh <|
      Term.mem_freeSupportList_of_mem
        (by simp) hMember
  have hArgumentFresh :
      (SetSort.set, resultId) ∉
        Term.freeSupport argument := by
    intro hMember
    exact hFresh <|
      Term.mem_freeSupportList_of_mem
        (by simp) hMember
  have hPredicate :
      Formula.Admissible predicate := by
    dsimp [predicate, guard]
    exact Formula.Admissible.conj
      (is_function_formula_admissible hFunction)
      (membership_formula_admissible hArgument
        (domain_term_admissible function hFunction))
  have hBody :
      Formula.Admissible body := by
    dsimp [body]
    exact graph_admissible data
      (ArgsAdmissible.cons hFunction <|
        ArgsAdmissible.cons hArgument
          ArgsAdmissible.nil)
      (set_variable_admissible resultId)
  have hExcluded :
      Derives mapping_predicate_theory []
        (predicate ∨ₘ ¬ₘ predicate) :=
    Derives.excluded_middle_m
      (hFormulaCheck :=
        Formula.check_certificate_of_admissible
          hPredicate)
  apply Derives.disj_elim
    (conclusion := conclusion)
    hExcluded
  ·
    let Γ : Context signature := [predicate]
    have hPredicateProof :
        Derives mapping_predicate_theory Γ predicate :=
      Derives.assumption_of_mem (by simp [Γ])
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible
            hPredicate)
    have hPairExists :
        Derives mapping_predicate_theory Γ
          (Formula.existsE SetSort.set <|
            ⟨argument, bₛ#0⟩ₘ ∈ₘ function) := by
      have hBase :=
        Derives.theory_weaken
          (fun _ hφ =>
            function_predicate_theory_subset_mapping_predicate_theory
              hφ)
          (guard_graph_value_exists
            function argument hFunction hArgument)
      exact Derives.imp_elim
        hBase.context_weaken_cons hPredicateProof
    let value :=
      FreshVariable.fresh_id SetSort.set
        [predicate, conclusion]
    let valueBody : SetFormula :=
      ⟨argument, x#value⟩ₘ ∈ₘ function
    have hValueFreshPredicate :
        (SetSort.set, value) ∉
          Formula.freeSupport predicate := by
      dsimp [value]
      exact FreshVariable.fresh_id_not_mem_m
        (by simp)
    have hValueFreshConclusion :
        (SetSort.set, value) ∉
          Formula.freeSupport conclusion := by
      dsimp [value]
      exact FreshVariable.fresh_id_not_mem_m
        (by simp)
    have hValueFreshFunction :
        (SetSort.set, value) ∉
          Term.freeSupport function := by
      intro hMember
      apply hValueFreshPredicate
      simp only [predicate, guard,
        Formula.freeSupport, domain_term,
        Term.freeSupport, Term.freeSupportList]
      exact List.mem_append_left _ <| by
        simpa using
          List.mem_append_left [] hMember
    have hValueFreshArgument :
        (SetSort.set, value) ∉
          Term.freeSupport argument := by
      intro hMember
      apply hValueFreshPredicate
      simp only [predicate, guard,
        Formula.freeSupport, domain_term,
        Term.freeSupport, Term.freeSupportList]
      exact List.mem_append_right _ <|
        List.mem_append_left _ hMember
    have hPairExists' :
        Derives mapping_predicate_theory Γ
          (Formula.existsE SetSort.set <|
            Formula.closeFreeAt SetSort.set
              value 0 valueBody) := by
      have hFunctionClose :
          Term.closeFreeAt SetSort.set value 0 function =
            function :=
        Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
          SetSort.set value 0 function
            hFunction.2 hValueFreshFunction
      have hArgumentClose :
          Term.closeFreeAt SetSort.set value 0 argument =
            argument :=
        Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
          SetSort.set value 0 argument
            hArgument.2 hValueFreshArgument
      simpa [valueBody, Formula.closeFreeAt,
        Term.closeFreeAt, ordered_pair_term,
        hFunctionClose, hArgumentClose] using
        hPairExists
    have hValueBody :
        Formula.Admissible valueBody := by
      dsimp [valueBody]
      exact membership_formula_admissible
        (ordered_pair_term_admissible
          argument (x#value) hArgument
          (set_variable_admissible value))
        hFunction
    have hCase :
        Derives mapping_predicate_theory
          (valueBody :: Γ) conclusion := by
      have hPair :
          Derives mapping_predicate_theory
            (valueBody :: Γ) valueBody :=
        Derives.assumption_of_mem (by simp)
          (hFormulaCheck :=
            Formula.check_certificate_of_admissible
              hValueBody)
      have hPositive :
          Derives mapping_predicate_theory
            (valueBody :: Γ) predicate := by
        exact hPredicateProof.context_weaken_cons
      have hGraph :
          Derives mapping_predicate_theory
            (valueBody :: Γ)
            (graph [function, argument]
              (x#value)) := by
        unfold graph
        apply Derives.conj_intro
        · apply Derives.imp_intro
            (hAntecedentCheck :=
              Formula.check_certificate_of_admissible
                hPredicate)
          exact hPair.context_weaken_cons
        · apply Derives.imp_intro
            (hAntecedentCheck :=
              Formula.check_certificate_of_admissible
                (Formula.Admissible.neg hPredicate))
          apply Derives.falsum_elim
            (hCheck :=
              Formula.check_certificate_of_admissible <|
                Formula.Admissible.equal
                  (set_variable_admissible value)
                  hFunction)
          exact Derives.neg_elim
            hPositive.context_weaken_cons
            (Derives.assumption_of_mem
              (by simp) :
              Derives mapping_predicate_theory
                ((¬ₘ predicate) ::
                  valueBody :: Γ)
                (¬ₘ predicate))
      unfold conclusion
      apply Derives.exists_intro_substituted
        (eigen := resultId)
        (witness := x#value)
      have hFunctionFixed :
          Term.substituteFree SetSort.set resultId
              (x#value) function =
            function :=
        Term.substituteFree_eq_self_of_not_mem
          SetSort.set resultId (x#value)
          function hFunctionFresh
      have hArgumentFixed :
          Term.substituteFree SetSort.set resultId
              (x#value) argument =
            argument :=
        Term.substituteFree_eq_self_of_not_mem
          SetSort.set resultId (x#value)
          argument hArgumentFresh
      simpa [body, graph, guard,
        Formula.substituteFree, Term.substituteFree,
        domain_term, ordered_pair_term,
        hFunctionFixed, hArgumentFixed] using
        hGraph
    exact Derives.exists_elim
      (by
        intro φ hφ
        rw [(mapping_predicate_theory_sentence
          hφ).2]
        simp)
      (by
        intro φ hφ
        rcases List.mem_singleton.mp hφ with rfl
        exact hValueFreshPredicate)
      hValueFreshConclusion
      hPairExists' hCase
  ·
    let Γ : Context signature := [¬ₘ predicate]
    have hNegative :
        Derives mapping_predicate_theory Γ
          (¬ₘ predicate) :=
      Derives.assumption_of_mem (by simp [Γ])
    have hGraph :
        Derives mapping_predicate_theory Γ
          (graph [function, argument] function) := by
      unfold graph
      apply Derives.conj_intro
      · apply Derives.imp_intro
          (hAntecedentCheck :=
            Formula.check_certificate_of_admissible
              hPredicate)
        apply Derives.falsum_elim
          (hCheck :=
            Formula.check_certificate_of_admissible <|
              membership_formula_admissible
                (ordered_pair_term_admissible
                  argument function
                  hArgument hFunction)
                hFunction)
        exact Derives.neg_elim
          (Derives.assumption_of_mem
            (by simp) :
            Derives mapping_predicate_theory
              (predicate :: Γ) predicate)
          hNegative.context_weaken_cons
      · apply Derives.imp_intro
          (hAntecedentCheck :=
            Formula.check_certificate_of_admissible
              (Formula.Admissible.neg hPredicate))
        exact Derives.context_weaken_cons <|
          Derives.eq_refl_m
            (T := mapping_predicate_theory)
            (Γ := Γ) function
            (sort := SetSort.set)
            (hTermCheck :=
              Term.check_certificate_of_admissible
                hFunction)
    unfold conclusion
    apply Derives.exists_intro_substituted
      (eigen := resultId)
      (witness := function)
    have hFunctionFixed :
        Term.substituteFree SetSort.set resultId
            function function =
          function :=
      Term.substituteFree_eq_self_of_not_mem
        SetSort.set resultId function
        function hFunctionFresh
    have hArgumentFixed :
        Term.substituteFree SetSort.set resultId
            function argument =
          argument :=
      Term.substituteFree_eq_self_of_not_mem
        SetSort.set resultId function
        argument hArgumentFresh
    simpa [body, graph, guard,
      Formula.substituteFree, Term.substituteFree,
      domain_term, ordered_pair_term,
      hFunctionFixed, hArgumentFixed] using
      hGraph

private theorem functional
    {arguments : List SetTerm}
    {left right : SetTerm}
    (hArguments :
      ArgsAdmissible arguments
        (signature.funcDomain FunctionSymbol.application))
    (hLeft :
      Term.Admissible left SetSort.set)
    (hRight :
      Term.Admissible right SetSort.set) :
    Derives mapping_predicate_theory [] <|
      Formula.imp (graph arguments left) <|
        Formula.imp (graph arguments right) <|
          Formula.equal left right := by
  change ArgsAdmissible arguments
    [SetSort.set, SetSort.set] at hArguments
  rcases pair_admissible hArguments with
    ⟨function, argument, rfl,
      hFunction, hArgument⟩
  let predicate := guard function argument
  let leftGraph := graph [function, argument] left
  let rightGraph := graph [function, argument] right
  let Γ : Context signature :=
    [rightGraph, leftGraph]
  have hPredicate :
      Formula.Admissible predicate := by
    dsimp [predicate, guard]
    exact Formula.Admissible.conj
      (is_function_formula_admissible hFunction)
      (membership_formula_admissible hArgument
        (domain_term_admissible function hFunction))
  have hLeftGraph :
      Formula.Admissible leftGraph := by
    dsimp [leftGraph]
    exact graph_admissible data
      (ArgsAdmissible.cons hFunction <|
        ArgsAdmissible.cons hArgument
          ArgsAdmissible.nil)
      hLeft
  have hRightGraph :
      Formula.Admissible rightGraph := by
    dsimp [rightGraph]
    exact graph_admissible data
      (ArgsAdmissible.cons hFunction <|
        ArgsAdmissible.cons hArgument
          ArgsAdmissible.nil)
      hRight
  apply Derives.imp_intro
    (hAntecedentCheck :=
      Formula.check_certificate_of_admissible
        hLeftGraph)
  apply Derives.imp_intro
    (hAntecedentCheck :=
      Formula.check_certificate_of_admissible
        hRightGraph)
  have hLeftProof :
      Derives mapping_predicate_theory Γ leftGraph :=
    Derives.assumption_of_mem (by simp [Γ])
      (hFormulaCheck :=
        Formula.check_certificate_of_admissible
          hLeftGraph)
  have hRightProof :
      Derives mapping_predicate_theory Γ rightGraph :=
    Derives.assumption_of_mem (by simp [Γ])
      (hFormulaCheck :=
        Formula.check_certificate_of_admissible
          hRightGraph)
  have hExcluded :
      Derives mapping_predicate_theory Γ
        (predicate ∨ₘ ¬ₘ predicate) :=
    Derives.excluded_middle_m
      (hFormulaCheck :=
        Formula.check_certificate_of_admissible
          hPredicate)
  apply Derives.disj_elim hExcluded
  ·
    have hPositive :
        Derives mapping_predicate_theory
          (predicate :: Γ) predicate :=
      Derives.assumption_of_mem (by simp)
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible
            hPredicate)
    have hLeftMembership :
        Derives mapping_predicate_theory
          (predicate :: Γ)
          (⟨argument, left⟩ₘ ∈ₘ function) := by
      have hImp :=
        Derives.conj_elim_left
          (hLeftProof.context_weaken_cons
            (assumption := predicate))
      exact Derives.imp_elim hImp hPositive
    have hRightMembership :
        Derives mapping_predicate_theory
          (predicate :: Γ)
          (⟨argument, right⟩ₘ ∈ₘ function) := by
      have hImp :=
        Derives.conj_elim_left
          (hRightProof.context_weaken_cons
            (assumption := predicate))
      exact Derives.imp_elim hImp hPositive
    have hFunctionFormula :=
      Derives.conj_elim_left hPositive
    have hSingle :=
      Derives.theory_weaken
        (fun _ hφ =>
          function_predicate_theory_subset_mapping_predicate_theory
            hφ)
        (is_function_single_valued
          function argument left right
          hFunction hArgument hLeft hRight)
    exact Derives.imp_elim
      (Derives.imp_elim
        (Derives.imp_elim
          (hSingle.context_weaken
            (by simp [Γ]))
          hFunctionFormula)
        hLeftMembership)
      hRightMembership
  ·
    have hNegative :
        Derives mapping_predicate_theory
          ((¬ₘ predicate) :: Γ)
          (¬ₘ predicate) :=
      Derives.assumption_of_mem (by simp)
    have hLeftEquality :
        Derives mapping_predicate_theory
          ((¬ₘ predicate) :: Γ)
          (left ≐ₘ function) := by
      have hImp :=
        Derives.conj_elim_right
          (hLeftProof.context_weaken_cons
            (assumption := ¬ₘ predicate))
      exact Derives.imp_elim hImp hNegative
    have hRightEquality :
        Derives mapping_predicate_theory
          ((¬ₘ predicate) :: Γ)
          (right ≐ₘ function) := by
      have hImp :=
        Derives.conj_elim_right
          (hRightProof.context_weaken_cons
            (assumption := ¬ₘ predicate))
      exact Derives.imp_elim hImp hNegative
    exact Metatheory.Derives.equality_trans
      hLeftEquality
      (Metatheory.Derives.equality_symm
        hRightEquality)

/-- 映射谓词理论给出的全体、单值函数求值图表示。 -/
def graph_presentation : GraphPresentation data where
  theory := mapping_predicate_theory
  theory_sentence := mapping_predicate_theory_sentence
  total := total
  functional := functional

/-- 映射谓词理论的固定公理均不含函数求值符号。 -/
private theorem base_formula_avoids
    {source : SetFormula}
    (hSource : mapping_predicate_theory source) :
    FormulaAvoids FunctionSymbol.application source := by
  simp only [mapping_predicate_theory,
    function_predicate_theory,
    equivalence_relation_theory,
    relation_composition_operator_theory,
    relation_composition_theory,
    relation_converse_operator_theory,
    relation_converse_theory,
    relation_plane_theory,
    relation_range_operator_theory,
    relation_range_theory,
    relation_domain_operator_theory,
    relation_domain_theory,
    relation_predicate_theory,
    relation_base_theory,
    right_projection_operator_theory,
    left_projection_operator_theory,
    relation_function_theory,
    ordered_pair_reverse_operator_theory,
    ordered_pair_operator_theory,
    singleton_operator_theory,
    pairing_operator_theory,
    pairing_theory,
    cartesian_product_operator_theory,
    cartesian_product_theory,
    cartesian_product_base_theory,
    power_set_operator_theory,
    power_set_theory,
    subset_theory,
    binary_union_operator_theory,
    binary_union_base_theory,
    union_operator_theory,
    union_theory,
    extensionality_theory,
    Theory.insert, Theory.union,
    Theory.singleton] at hSource
  repeat'
    first
    | obtain hSource | hSource := hSource
    | subst source
  all_goals
    apply checkFormulaAvoids_sound
    native_decide

/-- 三个外层 binder 打开后的函数求值定义实例。 -/
private def definition_point : SetFormula :=
  function_application_definition_instance
    (x#0) (x#1) (x#2)

/-- 函数求值定义实例消去求值项后的显式图正规形。 -/
private def compiled_definition_point : SetFormula :=
  guard (x#1) (x#3) ⟶ₘ
    (((∃ₘ[SetSort.set, 0],
        graph [x#1, x#3] (x#0) ∧ₘ
          ((x#5) ≐ₘ (x#0))) ↔ₘ
      (⟨x#3, x#5⟩ₘ ∈ₘ x#1)))

/-- 开放函数求值定义实例的编译只生成一个规范图见证。 -/
private theorem formula_definition_point :
    FunctionGraphElimination.formula data definition_point =
      compiled_definition_point := by
  unfold definition_point
    function_application_definition_instance
  simp [compiled_definition_point,
    FunctionGraphElimination.formula,
    FunctionGraphElimination.equality,
    FunctionGraphElimination.relation,
    FunctionGraphElimination.terms,
    FunctionGraphElimination.term,
    close_witnesses, condition_conjunction,
    data, graph, guard,
    domain_term, function_application_term,
    ordered_pair_term, source_id, witness_id]

/-- 映射谓词理论的公理在函数求值编译下严格保持原式。 -/
private theorem formula_base_eq
    {source : SetFormula}
    (hSource : mapping_predicate_theory source) :
    FunctionGraphElimination.formula data source =
      source := by
  apply formula_eq_of_sentence_avoids data source
  · exact base_formula_avoids hSource
  · exact mapping_predicate_theory_sentence hSource

/-- 映射谓词理论逐点证明编译后的函数求值定义公式。 -/
private theorem compiled_definition_point_derives :
    Derives mapping_predicate_theory []
      compiled_definition_point := by
  unfold compiled_definition_point
  let predicate := guard (x#1) (x#3)
  let witnessBody : SetFormula :=
    graph [x#1, x#3] (x#0) ∧ₘ
      ((x#5) ≐ₘ (x#0))
  let witnessExists : SetFormula :=
    ∃ₘ[SetSort.set, 0], witnessBody
  let membership : SetFormula :=
    ⟨x#3, x#5⟩ₘ ∈ₘ x#1
  have hPredicate :
      Formula.Admissible predicate := by
    dsimp [predicate, guard]
    exact Formula.Admissible.conj
      (is_function_formula_admissible
        (set_variable_admissible 1))
      (membership_formula_admissible
        (set_variable_admissible 3)
        (domain_term_admissible
          (x#1) (set_variable_admissible 1)))
  apply Derives.imp_intro
    (hAntecedentCheck :=
      Formula.check_certificate_of_admissible
        hPredicate)
  apply Derives.iff_intro
  ·
    let Γ : Context signature :=
      [witnessExists, predicate]
    have hExists :
        Derives mapping_predicate_theory Γ
          witnessExists :=
      Derives.assumption_of_mem (by simp [Γ])
    have hPredicateProof :
        Derives mapping_predicate_theory Γ
          predicate :=
      Derives.assumption_of_mem (by simp [Γ])
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible
            hPredicate)
    have hCase :
        Derives mapping_predicate_theory
          (witnessBody :: Γ) membership := by
      have hWitnessBody :
          Derives mapping_predicate_theory
            (witnessBody :: Γ) witnessBody :=
        Derives.assumption_of_mem (by simp)
      have hGraph :=
        Derives.conj_elim_left hWitnessBody
      have hValueEquality :
          Derives mapping_predicate_theory
            (witnessBody :: Γ)
            ((x#5) ≐ₘ (x#0)) :=
        Derives.conj_elim_right hWitnessBody
      have hWitnessMembership :
          Derives mapping_predicate_theory
            (witnessBody :: Γ)
            (⟨x#3, x#0⟩ₘ ∈ₘ x#1) := by
        have hImp :=
          Derives.conj_elim_left hGraph
        exact Derives.imp_elim hImp
          hPredicateProof.context_weaken_cons
      have hPairEquality :
          Derives mapping_predicate_theory
            (witnessBody :: Γ)
            (⟨x#3, x#5⟩ₘ ≐ₘ
              ⟨x#3, x#0⟩ₘ) := by
        exact
          Metatheory.Derives.binary_term_constructor_congr_of_equalities
            ordered_pair_term
            ordered_pair_term_admissible
            (by
              intros
              simp [Term.substituteFree])
            (x#3) (x#3) (x#5) (x#0)
            (set_variable_admissible 3)
            (set_variable_admissible 3)
            (set_variable_admissible 5)
            (set_variable_admissible 0)
            (Derives.eq_refl_m
              (T := mapping_predicate_theory)
              (Γ := witnessBody :: Γ)
              (x#3))
            hValueEquality
      have hMembershipIff :=
        membership_left_iff_of_equality
          (⟨x#3, x#5⟩ₘ)
          (⟨x#3, x#0⟩ₘ)
          (x#1)
          (ordered_pair_term_admissible
            (x#3) (x#5)
            (set_variable_admissible 3)
            (set_variable_admissible 5))
          (ordered_pair_term_admissible
            (x#3) (x#0)
            (set_variable_admissible 3)
            (set_variable_admissible 0))
          (set_variable_admissible 1)
          hPairEquality
      exact Derives.iff_elim_left
        hMembershipIff hWitnessMembership
    exact Derives.exists_elim
      (sort := SetSort.set)
      (eigen := 0)
      (body := witnessBody)
      (conclusion := membership)
      (by
        intro φ hφ
        rw [(mapping_predicate_theory_sentence
          hφ).2]
        simp)
      (by
        intro φ hφ
        rcases List.mem_cons.mp hφ with
          rfl | hφ
        · native_decide
        · rcases List.mem_singleton.mp hφ with rfl
          native_decide)
      (by native_decide)
      (by simpa [witnessExists] using hExists)
      hCase
  ·
    let Γ : Context signature :=
      [membership, predicate]
    have hMembership :
        Derives mapping_predicate_theory Γ
          membership :=
      Derives.assumption_of_mem (by simp [Γ])
    have hPredicateProof :
        Derives mapping_predicate_theory Γ
          predicate :=
      Derives.assumption_of_mem (by simp [Γ])
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible
            hPredicate)
    have hGraph :
        Derives mapping_predicate_theory Γ
          (graph [x#1, x#3] (x#5)) := by
      unfold graph
      apply Derives.conj_intro
      · apply Derives.imp_intro
          (hAntecedentCheck :=
            Formula.check_certificate_of_admissible
              hPredicate)
        exact hMembership.context_weaken_cons
      · apply Derives.imp_intro
          (hAntecedentCheck :=
            Formula.check_certificate_of_admissible
              (Formula.Admissible.neg hPredicate))
        apply Derives.falsum_elim
          (hCheck :=
            Formula.check_certificate_of_admissible <|
              Formula.Admissible.equal
                (set_variable_admissible 5)
                (set_variable_admissible 1))
        exact Derives.neg_elim
          hPredicateProof.context_weaken_cons
          (Derives.assumption_of_mem
            (by simp) :
            Derives mapping_predicate_theory
              ((¬ₘ predicate) :: Γ)
              (¬ₘ predicate))
    have hConjunction :
        Derives mapping_predicate_theory Γ
          (graph [x#1, x#3] (x#5) ∧ₘ
            ((x#5) ≐ₘ (x#5))) :=
      Derives.conj_intro hGraph <|
        Derives.eq_refl_m
          (T := mapping_predicate_theory)
          (Γ := Γ) (x#5)
    apply Derives.exists_intro_substituted
      (eigen := 0) (witness := x#5)
    simpa [witnessBody, graph, guard,
      Formula.substituteFree,
      Term.substituteFree,
      domain_term, ordered_pair_term] using
      hConjunction

/-- 映射谓词理论证明完整函数求值定义公理的函数图编译。 -/
private theorem formula_definition_axiom_derives :
    Derives mapping_predicate_theory []
      (FunctionGraphElimination.formula
        data function_application_definition_axiom) := by
  have hPoint :
      Derives mapping_predicate_theory []
        (FunctionGraphElimination.formula
          data definition_point) := by
    rw [formula_definition_point]
    exact compiled_definition_point_derives
  have hPointAdmissible :
      Formula.Admissible definition_point :=
    function_application_definition_instance_admissible
      (set_variable_admissible 0)
      (set_variable_admissible 1)
      (set_variable_admissible 2)
  have hValue :=
    graph_presentation.formula_forall_close_derives
      SetSort.set 2 definition_point
      hPointAdmissible hPoint
  have hValueAdmissible :
      Formula.Admissible
        (Formula.forallE SetSort.set
          (Formula.closeFreeAt SetSort.set
            2 0 definition_point)) :=
    Formula.Admissible.forall_closeFreeAt
      SetSort.set 2 hPointAdmissible
  have hArgument :=
    graph_presentation.formula_forall_close_derives
      SetSort.set 1
      (Formula.forallE SetSort.set
        (Formula.closeFreeAt SetSort.set
          2 0 definition_point))
      hValueAdmissible hValue
  have hArgumentAdmissible :
      Formula.Admissible
        (Formula.forallE SetSort.set
          (Formula.closeFreeAt SetSort.set 1 0
            (Formula.forallE SetSort.set
              (Formula.closeFreeAt SetSort.set
                2 0 definition_point)))) :=
    Formula.Admissible.forall_closeFreeAt
      SetSort.set 1 hValueAdmissible
  have hFunction :=
    graph_presentation.formula_forall_close_derives
      SetSort.set 0
      (Formula.forallE SetSort.set
        (Formula.closeFreeAt SetSort.set 1 0
          (Formula.forallE SetSort.set
            (Formula.closeFreeAt SetSort.set
              2 0 definition_point))))
      hArgumentAdmissible hArgument
  simpa [function_application_definition_axiom,
    definition_point] using hFunction

private theorem compile_axiom
    {source : SetFormula}
    (hSource : function_application_theory source) :
    Derives mapping_predicate_theory []
      (FunctionGraphElimination.formula
        data source) := by
  rcases hSource with rfl | hSource
  · exact formula_definition_axiom_derives
  · rw [formula_base_eq hSource]
    exact Derives.theory_mem hSource
      (hFormulaCheck :=
        Formula.check_certificate_of_admissible
          (mapping_predicate_theory_admissible
            source hSource))

/--
函数求值扩张的理论级函数图消去表示。

该表示足以把 checked/Hilbert 证明整体翻译到映射谓词理论。现有求值公理在 guard
外不约束函数项，因此这里刻意不伪造要求无条件 `realizes` 的
`DefinitionPresentation`。
-/
def theory_presentation :
    TheoryPresentation data where
  graph := graph_presentation
  source := function_application_theory
  compile_axiom := compile_axiom

theorem hilbert
    {source : SetFormula}
    (hSource :
      HilbertDerives function_application_theory source) :
    Derives mapping_predicate_theory []
      (FunctionGraphElimination.formula
        data source) :=
  theory_presentation.hilbert hSource

/-- 函数求值扩张的 checked 自然演绎证明可整体翻译到映射谓词理论。 -/
theorem derives
    {source : SetFormula}
    (hSource :
      Derives function_application_theory [] source) :
    Derives mapping_predicate_theory []
      (FunctionGraphElimination.formula
        data source) :=
  theory_presentation.derives SetSort.set hSource

theorem hilbert_falsum
    (hSource :
      HilbertDerives function_application_theory
        Formula.falsum) :
    Derives mapping_predicate_theory []
      Formula.falsum :=
  theory_presentation.hilbert_falsum hSource

theorem derives_falsum
    (hSource :
      Derives function_application_theory []
        Formula.falsum) :
    Derives mapping_predicate_theory []
      Formula.falsum :=
  theory_presentation.derives_falsum
    SetSort.set hSource

theorem consistent
    (hBase :
      Derives.Consistent mapping_predicate_theory []) :
    Derives.Consistent function_application_theory [] :=
  theory_presentation.consistent SetSort.set hBase

theorem hilbert_consistent
    (hBase :
      Derives.Consistent mapping_predicate_theory []) :
    ¬ HilbertDerives function_application_theory
        Formula.falsum :=
  theory_presentation.hilbert_consistent hBase

end FunctionApplication
end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
