import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Relation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Hilbert

/-
# 定义域函数的证明级图消去

定义域函数只在输入为关系时由分离规格确定。图在关系谓词外回退为输入项本身，
因此它可以作为全体、单值的函数图；定义公理的编译仍由关系守卫负责。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace FunctionGraphElimination
namespace RelationDomain

open Nonlogical.BasicSetTheory
open scoped Symbols

set_option autoImplicit false

def guard (relation : SetTerm) : SetFormula :=
  is_relation_formula relation

def graph : List SetTerm → SetTerm → SetFormula
  | (relation :: []), result =>
      (guard relation ⟶ₘ
        relation_domain_spec relation result) ∧ₘ
      ((¬ₘ guard relation) ⟶ₘ
        (result ≐ₘ relation))
  | _, _ =>
      Formula.falsum

private theorem union_well_sorted
    {source : SetTerm}
    (hSource : TermWellSorted source SetSort.set) :
    TermWellSorted (union_term source) SetSort.set := by
  simpa [union_term, signature] using
    (TermWellSorted.app
      (σ := signature) FunctionSymbol.union
      (ArgsWellSorted.cons hSource
        ArgsWellSorted.nil))

private theorem double_union_well_sorted
    {relation : SetTerm}
    (hRelation : TermWellSorted relation SetSort.set) :
    TermWellSorted (double_union_term relation) SetSort.set := by
  exact union_well_sorted
    (union_well_sorted hRelation)

private theorem left_projection_well_sorted
    {pair : SetTerm}
    (hPair : TermWellSorted pair SetSort.set) :
    TermWellSorted (left_projection_term pair) SetSort.set := by
  simpa [left_projection_term, signature] using
    (TermWellSorted.app
      (σ := signature) FunctionSymbol.leftProjection
      (ArgsWellSorted.cons hPair
        ArgsWellSorted.nil))

private theorem spec_well_formed
    {relation candidate : SetTerm}
    (hRelation : TermWellSorted relation SetSort.set)
    (hCandidate : TermWellSorted candidate SetSort.set) :
    FormulaWellFormed
      (relation_domain_spec relation candidate) := by
  unfold relation_domain_spec relation_coordinate_spec
  apply FormulaWellFormed.forallE
  apply FormulaWellFormed.iff
  · apply FormulaWellFormed.rel
    simpa [signature] using
      (ArgsWellSorted.cons
        (TermWellSorted.bvar SetSort.set 0)
        (ArgsWellSorted.cons hCandidate
          ArgsWellSorted.nil))
  · apply FormulaWellFormed.conj
    · apply FormulaWellFormed.rel
      simpa [signature] using
        (ArgsWellSorted.cons
          (TermWellSorted.bvar SetSort.set 0)
          (ArgsWellSorted.cons
            (double_union_well_sorted hRelation)
            ArgsWellSorted.nil))
    · apply FormulaWellFormed.existsE
      apply FormulaWellFormed.conj
      · apply FormulaWellFormed.rel
        simpa [signature] using
          (ArgsWellSorted.cons
            (TermWellSorted.bvar SetSort.set 0)
            (ArgsWellSorted.cons hRelation
              ArgsWellSorted.nil))
      · exact FormulaWellFormed.equal
          (TermWellSorted.bvar
            (σ := signature) SetSort.set 1)
          (left_projection_well_sorted
            (TermWellSorted.bvar
              (σ := signature) SetSort.set 0))

private theorem push_scoped
    {scope : Scope signature} {term : SetTerm}
    (hTerm : TermScoped scope term) :
    TermScoped (Scope.push scope SetSort.set) term := by
  apply Term.scoped_mono hTerm
  intro sort
  cases sort
  simp [Scope.push]

private theorem union_scoped
    {scope : Scope signature} {source : SetTerm}
    (hSource : TermScoped scope source) :
    TermScoped scope (union_term source) := by
  simpa [union_term] using
    (TermScoped.app
      (σ := signature) (ctx := scope)
      FunctionSymbol.union [source]
      (by
        intro term hTerm
        simpa using
          (List.mem_singleton.mp hTerm ▸ hSource)))

private theorem double_union_scoped
    {scope : Scope signature} {relation : SetTerm}
    (hRelation : TermScoped scope relation) :
    TermScoped scope (double_union_term relation) := by
  exact union_scoped (union_scoped hRelation)

private theorem left_projection_scoped
    {scope : Scope signature} {pair : SetTerm}
    (hPair : TermScoped scope pair) :
    TermScoped scope (left_projection_term pair) := by
  simpa [left_projection_term] using
    (TermScoped.app
      (σ := signature) (ctx := scope)
      FunctionSymbol.leftProjection [pair]
      (by
        intro term hTerm
        simpa using
          (List.mem_singleton.mp hTerm ▸ hPair)))

private theorem spec_scoped
    {scope : Scope signature}
    {relation candidate : SetTerm}
    (hRelation : TermScoped scope relation)
    (hCandidate : TermScoped scope candidate) :
    FormulaScoped scope
      (relation_domain_spec relation candidate) := by
  unfold relation_domain_spec relation_coordinate_spec
  apply FormulaScoped.forallE
  apply FormulaScoped.iff
  · exact FormulaScoped.rel
      (σ := signature)
      RelationSymbol.membership
      [bₛ#0, candidate] <| by
        intro term hTerm
        rcases List.mem_cons.mp hTerm with
          rfl | hTerm
        · exact TermScoped.bvar (by simp [Scope.push])
        · rcases List.mem_singleton.mp hTerm with rfl
          exact push_scoped hCandidate
  · apply FormulaScoped.conj
    · exact FormulaScoped.rel
        (σ := signature)
        RelationSymbol.membership
        [bₛ#0, double_union_term relation] <| by
          intro term hTerm
          rcases List.mem_cons.mp hTerm with
            rfl | hTerm
          · exact TermScoped.bvar (by simp [Scope.push])
          · rcases List.mem_singleton.mp hTerm with rfl
            exact push_scoped
              (double_union_scoped hRelation)
    · apply FormulaScoped.existsE
      apply FormulaScoped.conj
      · exact FormulaScoped.rel
          (σ := signature)
          RelationSymbol.membership
          [bₛ#0, relation] <| by
            intro term hTerm
            rcases List.mem_cons.mp hTerm with
              rfl | hTerm
            · exact TermScoped.bvar
                (by simp [Scope.push])
            · rcases List.mem_singleton.mp hTerm with rfl
              exact push_scoped (push_scoped hRelation)
      · apply FormulaScoped.equal
        · exact TermScoped.bvar (by simp [Scope.push])
        · exact left_projection_scoped
            (TermScoped.bvar (by simp [Scope.push]))

private theorem graph_well_formed
    {arguments : List SetTerm} {result : SetTerm}
    (hArguments :
      ArgsWellSorted arguments
        (signature.funcDomain FunctionSymbol.domain))
    (hResult :
      TermWellSorted result SetSort.set) :
    FormulaWellFormed (graph arguments result) := by
  change ArgsWellSorted arguments [SetSort.set] at hArguments
  cases arguments with
  | nil =>
      simpa [graph] using
        (FormulaWellFormed.falsum :
          FormulaWellFormed
            (Formula.falsum : SetFormula))
  | cons relation tail =>
      cases tail with
      | nil =>
          rcases hArguments with ⟨⟩
          rename_i hRelation hNil
          cases hNil
          have hRelationFormula :
              FormulaWellFormed
                (is_relation_formula relation) := by
            apply FormulaWellFormed.rel
            simpa [signature] using
              (ArgsWellSorted.cons hRelation
                ArgsWellSorted.nil)
          have hGuard :
              FormulaWellFormed (guard relation) :=
            hRelationFormula
          have hSpec :
              FormulaWellFormed
                (relation_domain_spec relation result) :=
            spec_well_formed hRelation hResult
          apply FormulaWellFormed.conj
          · exact FormulaWellFormed.imp
              hGuard hSpec
          · exact FormulaWellFormed.imp
              (FormulaWellFormed.neg hGuard)
              (FormulaWellFormed.equal hResult hRelation)
      | cons extra rest =>
          simpa [graph] using
            (FormulaWellFormed.falsum :
              FormulaWellFormed
                (Formula.falsum : SetFormula))

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
  | cons relation tail =>
      cases tail with
      | nil =>
          have hRelation := hArguments relation (by simp)
          have hGuard :
              FormulaScoped scope (guard relation) := by
            change FormulaScoped scope
              (Formula.rel RelationSymbol.isRelation
                [relation])
            exact FormulaScoped.rel
              (σ := signature)
              RelationSymbol.isRelation
              [relation] <| by
                intro term hTerm
                rcases List.mem_singleton.mp hTerm with rfl
                exact hRelation
          exact FormulaScoped.conj
            (FormulaScoped.imp
              hGuard
              (spec_scoped hRelation hResult))
            (FormulaScoped.imp
              (FormulaScoped.neg hGuard)
              (FormulaScoped.equal hResult hRelation))
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
  | cons relation tail =>
      cases tail with
      | nil =>
          simpa [graph, guard,
            relation_domain_spec,
            relation_coordinate_spec,
            relation_coordinate_projection_term,
            double_union_term,
            Formula.freeSupport,
            Term.freeSupport,
            Term.freeSupportList,
            left_projection_term,
            union_term,
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
  | cons relation tail =>
      cases tail with
      | nil =>
          cases target
          simp [graph, guard,
            relation_domain_spec,
            relation_coordinate_spec,
            relation_coordinate_projection_term,
            double_union_term,
            Formula.substituteFree,
            Term.substituteFree,
            left_projection_term,
            union_term]
      | cons extra rest =>
          simp [graph, Formula.substituteFree]

private theorem graph_avoids
    {arguments : List SetTerm} {result : SetTerm}
    (hArguments :
      TermsAvoid FunctionSymbol.domain arguments)
    (hResult :
      TermAvoids FunctionSymbol.domain result) :
    FormulaAvoids FunctionSymbol.domain
      (graph arguments result) := by
  cases arguments with
  | nil =>
      simp [graph, FormulaAvoids]
  | cons relation tail =>
      cases tail with
      | nil =>
          have hRelation :=
            hArguments relation (by simp)
          simp [graph, guard,
            relation_domain_spec,
            relation_coordinate_spec,
            relation_coordinate_projection_term,
            double_union_term,
            FormulaAvoids, TermsAvoid,
            TermAvoids, left_projection_term,
            union_term, hRelation, hResult]
      | cons extra rest =>
          simp [graph, FormulaAvoids]

def data : Data signature where
  symbol := FunctionSymbol.domain
  sort := SetSort.set
  codomain_eq := rfl
  graph := graph
  graph_well_formed := graph_well_formed
  graph_scoped := graph_scoped
  graph_freeSupport := graph_freeSupport
  graph_substituteFree := graph_substituteFree
  graph_avoids := graph_avoids

private theorem unary_admissible
    {arguments : List SetTerm}
    (hArguments :
      ArgsAdmissible arguments
        [SetSort.set]) :
    ∃ relation,
      arguments = [relation] ∧
        Term.Admissible relation SetSort.set := by
  rcases hArguments with ⟨hSorted, hScoped⟩
  cases hSorted with
  | cons hRelation hNil =>
      cases hNil
      exact ⟨_, rfl,
        ⟨hRelation,
          hScoped _ (by simp)⟩⟩

private theorem total
    {arguments : List SetTerm}
    (resultId : FreeVarId)
    (hArguments :
      ArgsAdmissible arguments
        (signature.funcDomain FunctionSymbol.domain))
    (hFresh :
      (SetSort.set, resultId) ∉
        Term.freeSupportList arguments) :
    Derives relation_domain_theory [] <|
      Formula.existsE SetSort.set <|
        Formula.closeFreeAt SetSort.set resultId 0 <|
          graph arguments <|
            .var (.fvar SetSort.set resultId) := by
  change ArgsAdmissible arguments [SetSort.set] at hArguments
  rcases unary_admissible hArguments with
    ⟨relation, rfl, hRelation⟩
  let predicate := guard relation
  let body : SetFormula := graph [relation] (x#resultId)
  let conclusion : SetFormula :=
    Formula.existsE SetSort.set <|
      Formula.closeFreeAt SetSort.set resultId 0 body
  have hRelationFresh :
      (SetSort.set, resultId) ∉
        Term.freeSupport relation := by
    intro hMember
    exact hFresh <|
      Term.mem_freeSupportList_of_mem
        (by simp) hMember
  have hPredicate :
      Formula.Admissible predicate := by
    simpa [predicate, guard] using
      is_relation_formula_admissible hRelation
  have hBody :
      Formula.Admissible body := by
    dsimp [body]
    exact graph_admissible data
      (ArgsAdmissible.cons hRelation
        ArgsAdmissible.nil)
      (set_variable_admissible resultId)
  have hExcluded :
      Derives relation_domain_theory []
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
        Derives relation_domain_theory Γ predicate :=
      Derives.assumption_of_mem
        (by simp [Γ])
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible
            hPredicate)
    have hExists :
        Derives relation_domain_theory Γ
          (relation_domain_exists relation) :=
      (relation_domain_exists_derives
        relation hRelation).context_weaken_cons
    let value :=
      FreshVariable.fresh_id SetSort.set
        [predicate, conclusion]
    let valueBody : SetFormula :=
      relation_domain_spec relation (x#value)
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
    have hValueFreshRelation :
        (SetSort.set, value) ∉
          Term.freeSupport relation := by
      intro hMember
      apply hValueFreshPredicate
      simpa [predicate, guard,
        Formula.freeSupport, Term.freeSupport,
        Term.freeSupportList] using
        List.mem_append_left [] hMember
    have hExists' :
        Derives relation_domain_theory Γ
          (Formula.existsE SetSort.set
            (Formula.closeFreeAt SetSort.set
              value 0 valueBody)) := by
      have hRelationClose (depth : Nat) :
          Term.closeFreeAt SetSort.set value depth relation =
            relation :=
        Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
          SetSort.set value depth relation
          hRelation.2 hValueFreshRelation
      simpa [valueBody, relation_domain_exists,
        relation_coordinate_exists,
        relation_coordinate_spec,
        relation_coordinate_projection_term,
        double_union_term,
        Formula.closeFreeAt,
        Formula.next_depth,
        Term.closeFreeAt,
        left_projection_term, union_term,
        hRelationClose] using hExists
    have hValueBody :
        Formula.Admissible valueBody := by
      exact relation_coordinate_spec_admissible
        (coordinate := RelationCoordinate.domain)
        hRelation
        (set_variable_admissible value)
    have hCase :
        Derives relation_domain_theory
          (valueBody :: Γ) conclusion := by
      have hSpec :
          Derives relation_domain_theory
            (valueBody :: Γ) valueBody :=
        Derives.assumption_of_mem
          (by simp)
          (hFormulaCheck :=
            Formula.check_certificate_of_admissible
              hValueBody)
      have hPositive :
          Derives relation_domain_theory
            (valueBody :: Γ) predicate :=
        hPredicateProof.context_weaken_cons
      have hGraph :
          Derives relation_domain_theory
            (valueBody :: Γ)
            (graph [relation] (x#value)) := by
        unfold graph
        apply Derives.conj_intro
        · apply Derives.imp_intro
            (hAntecedentCheck :=
              Formula.check_certificate_of_admissible
                hPredicate)
          exact hSpec.context_weaken_cons
        · apply Derives.imp_intro
            (hAntecedentCheck :=
              Formula.check_certificate_of_admissible
                (Formula.Admissible.neg hPredicate))
          apply Derives.falsum_elim
            (hCheck :=
              Formula.check_certificate_of_admissible
                (Formula.Admissible.equal
                  (set_variable_admissible value)
                  hRelation))
          exact Derives.neg_elim
            hPositive.context_weaken_cons
            (Derives.assumption_of_mem
              (by simp) :
              Derives relation_domain_theory
                ((¬ₘ predicate) ::
                  valueBody :: Γ)
                (¬ₘ predicate))
      unfold conclusion
      apply Derives.exists_intro_substituted
        (eigen := resultId)
        (witness := x#value)
      have hRelationFixed :
          Term.substituteFree SetSort.set resultId
              (x#value) relation =
            relation :=
        Term.substituteFree_eq_self_of_not_mem
          SetSort.set resultId (x#value)
          relation hRelationFresh
      simpa [body, graph, guard,
        relation_domain_spec,
        relation_coordinate_spec,
        relation_coordinate_projection_term,
        double_union_term,
        Formula.substituteFree,
        Term.substituteFree, left_projection_term,
        union_term, hRelationFixed] using hGraph
    exact Derives.exists_elim
      (by
        intro φ hφ
        rw [(relation_domain_theory_sentence hφ).2]
        simp)
      (by
        intro φ hφ
        rcases List.mem_singleton.mp hφ with rfl
        exact hValueFreshPredicate)
      hValueFreshConclusion hExists' hCase
  ·
    let Γ : Context signature := [¬ₘ predicate]
    have hNegative :
        Derives relation_domain_theory Γ
          (¬ₘ predicate) :=
      Derives.assumption_of_mem (by simp [Γ])
    have hGraph :
        Derives relation_domain_theory Γ
          (graph [relation] relation) := by
      unfold graph
      apply Derives.conj_intro
      · apply Derives.imp_intro
          (hAntecedentCheck :=
            Formula.check_certificate_of_admissible
              hPredicate)
        apply Derives.falsum_elim
          (hCheck :=
            Formula.check_certificate_of_admissible
              (relation_coordinate_spec_admissible
                (coordinate := RelationCoordinate.domain)
                hRelation hRelation))
        exact Derives.neg_elim
          (Derives.assumption_of_mem
            (by simp) :
            Derives relation_domain_theory
              (predicate :: Γ) predicate)
          hNegative.context_weaken_cons
      · apply Derives.imp_intro
          (hAntecedentCheck :=
            Formula.check_certificate_of_admissible
              (Formula.Admissible.neg hPredicate))
        exact Derives.context_weaken_cons <|
          Derives.eq_refl_m
            (T := relation_domain_theory)
            (Γ := Γ) relation
            (sort := SetSort.set)
            (hTermCheck :=
              Term.check_certificate_of_admissible
                hRelation)
    unfold conclusion
    apply Derives.exists_intro_substituted
      (eigen := resultId)
      (witness := relation)
    have hRelationFixed :
        Term.substituteFree SetSort.set resultId
            relation relation =
          relation :=
      Term.substituteFree_eq_self_of_not_mem
        SetSort.set resultId relation
        relation hRelationFresh
    simpa [body, graph, guard,
      relation_domain_spec,
      relation_coordinate_spec,
      relation_coordinate_projection_term,
      double_union_term,
      Formula.substituteFree,
      Term.substituteFree, left_projection_term,
      union_term, hRelationFixed] using
      hGraph

private theorem functional
    {arguments : List SetTerm}
    {left right : SetTerm}
    (hArguments :
      ArgsAdmissible arguments
        (signature.funcDomain FunctionSymbol.domain))
    (hLeft :
      Term.Admissible left SetSort.set)
    (hRight :
      Term.Admissible right SetSort.set) :
    Derives relation_domain_theory [] <|
      Formula.imp (graph arguments left) <|
        Formula.imp (graph arguments right) <|
          Formula.equal left right := by
  change ArgsAdmissible arguments [SetSort.set] at hArguments
  rcases unary_admissible hArguments with
    ⟨relation, rfl, hRelation⟩
  let predicate := guard relation
  let leftGraph := graph [relation] left
  let rightGraph := graph [relation] right
  let Γ : Context signature :=
    [rightGraph, leftGraph]
  have hPredicate :
      Formula.Admissible predicate := by
    simpa [predicate, guard] using
      is_relation_formula_admissible hRelation
  have hLeftGraph :
      Formula.Admissible leftGraph := by
    dsimp [leftGraph]
    exact graph_admissible data
      (ArgsAdmissible.cons hRelation
        ArgsAdmissible.nil) hLeft
  have hRightGraph :
      Formula.Admissible rightGraph := by
    dsimp [rightGraph]
    exact graph_admissible data
      (ArgsAdmissible.cons hRelation
        ArgsAdmissible.nil) hRight
  apply Derives.imp_intro
    (hAntecedentCheck :=
      Formula.check_certificate_of_admissible
        hLeftGraph)
  apply Derives.imp_intro
    (hAntecedentCheck :=
      Formula.check_certificate_of_admissible
        hRightGraph)
  have hLeftProof :
      Derives relation_domain_theory Γ leftGraph :=
    Derives.assumption_of_mem
      (by simp [Γ])
  have hRightProof :
      Derives relation_domain_theory Γ rightGraph :=
    Derives.assumption_of_mem
      (by simp [Γ])
  have hExcluded :
      Derives relation_domain_theory Γ
        (predicate ∨ₘ ¬ₘ predicate) :=
    Derives.excluded_middle_m
      (hFormulaCheck :=
        Formula.check_certificate_of_admissible
          hPredicate)
  apply Derives.disj_elim hExcluded
  ·
    have hPositive :
        Derives relation_domain_theory
          (predicate :: Γ) predicate :=
      Derives.assumption_of_mem (by simp)
    have hLeftSpec :
        Derives relation_domain_theory
          (predicate :: Γ)
          (relation_domain_spec relation left) := by
      exact Derives.imp_elim
        (Derives.conj_elim_left
          hLeftProof.context_weaken_cons)
        hPositive
    have hRightSpec :
        Derives relation_domain_theory
          (predicate :: Γ)
          (relation_domain_spec relation right) := by
      exact Derives.imp_elim
        (Derives.conj_elim_left
          hRightProof.context_weaken_cons)
        hPositive
    have hUnique :
        Derives relation_domain_theory
          (predicate :: Γ)
          (relation_domain_spec relation left ⟶ₘ
            relation_domain_spec relation right ⟶ₘ
              (left ≐ₘ right)) := by
      have hBase :=
        Derives.theory_weaken
          (fun _ hFormula =>
            relation_base_theory_subset_relation_domain_theory
              hFormula)
          (relation_domain_unique
            relation left right hRelation hLeft hRight)
      exact hBase.context_weaken (by simp)
    exact Derives.imp_elim
      (Derives.imp_elim
        hUnique
        hLeftSpec)
      hRightSpec
  ·
    have hNegative :
        Derives relation_domain_theory
          ((¬ₘ predicate) :: Γ)
          (¬ₘ predicate) :=
      Derives.assumption_of_mem (by simp)
    have hLeftEq :
        Derives relation_domain_theory
          ((¬ₘ predicate) :: Γ)
          (left ≐ₘ relation) := by
      exact Derives.imp_elim
        (Derives.conj_elim_right
          hLeftProof.context_weaken_cons)
        hNegative
    have hRightEq :
        Derives relation_domain_theory
          ((¬ₘ predicate) :: Γ)
          (right ≐ₘ relation) := by
      exact Derives.imp_elim
        (Derives.conj_elim_right
          hRightProof.context_weaken_cons)
        hNegative
    exact Metatheory.Derives.equality_trans
      hLeftEq
      (Metatheory.Derives.equality_symm hRightEq)

def graph_presentation : GraphPresentation data where
  theory := relation_domain_theory
  theory_sentence := relation_domain_theory_sentence
  total := total
  functional := functional

private theorem base_formula_avoids
    {source : SetFormula}
    (hSource : relation_domain_theory source) :
    FormulaAvoids FunctionSymbol.domain source := by
  simp only [relation_domain_theory,
    relation_predicate_theory,
    relation_base_theory,
    right_projection_operator_theory,
    left_projection_operator_theory,
    relation_function_theory,
    ordered_pair_operator_theory,
    singleton_operator_theory,
    pairing_operator_theory,
    pairing_theory,
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

private def definition_point : SetFormula :=
  domain_definition_instance (x#0) (x#1)

private def compiled_definition_point : SetFormula :=
  guard (x#1) ⟶ₘ
    (((∃ₘ[SetSort.set, 0],
        graph [x#1] (x#0) ∧ₘ
          ((x#3) ≐ₘ (x#0))) ↔ₘ
      relation_domain_spec (x#1) (x#3)))

private theorem formula_definition_point :
    FunctionGraphElimination.formula data definition_point =
      compiled_definition_point := by
  unfold definition_point domain_definition_instance
  have hSpec :
      FormulaAvoids FunctionSymbol.domain
        (relation_domain_spec (x#0) (x#1)) := by
    simp [FormulaAvoids, TermsAvoid, TermAvoids,
      relation_domain_spec, relation_coordinate_spec,
      relation_coordinate_projection_term,
      double_union_term, left_projection_term,
      union_term]
  have hSpecDirect :
      formula data (relation_domain_spec (x#0) (x#1)) =
        relation_domain_spec (x#1) (x#3) := by
    rw [formula_eq_source_of_avoids data
      (relation_domain_spec (x#0) (x#1)) hSpec]
    simp [relation_domain_spec, relation_coordinate_spec,
      relation_coordinate_projection_term,
      double_union_term, left_projection_term,
      union_term, source_formula, source_term, source_id]
  simp [compiled_definition_point,
    FunctionGraphElimination.formula,
    FunctionGraphElimination.equality,
    FunctionGraphElimination.relation,
    FunctionGraphElimination.terms,
    FunctionGraphElimination.term,
    close_witnesses, condition_conjunction,
    data, graph, guard,
    domain_term, source_id, witness_id]
  exact hSpecDirect

private theorem formula_base_eq
    {source : SetFormula}
    (hSource : relation_domain_theory source) :
    FunctionGraphElimination.formula data source =
      source := by
  apply formula_eq_of_sentence_avoids data source
  · exact base_formula_avoids hSource
  · exact relation_domain_theory_sentence hSource

private theorem theory_fresh
    (id : FreeVarId) :
    ∀ source, relation_domain_theory source →
      (SetSort.set, id) ∉
        Formula.freeSupport source := by
  intro source hSource
  rw [(graph_presentation.theory_sentence
    hSource).2]
  exact List.not_mem_nil

private theorem compiled_definition_point_derives :
    Derives relation_domain_theory []
      compiled_definition_point := by
  unfold compiled_definition_point
  let predicate := guard (x#1)
  let witnessBody : SetFormula :=
    graph [x#1] (x#0) ∧ₘ
      ((x#3) ≐ₘ (x#0))
  let witnessExists : SetFormula :=
    ∃ₘ[SetSort.set, 0], witnessBody
  let target : SetFormula :=
    relation_domain_spec (x#1) (x#3)
  apply Derives.imp_intro
    (hAntecedentCheck :=
      Formula.check_certificate_of_admissible
        (is_relation_formula_admissible
          (set_variable_admissible 1)))
  apply Derives.iff_intro
  ·
    let Γ : Context signature :=
      [witnessExists, predicate]
    have hExists :
        Derives relation_domain_theory Γ witnessExists :=
      Derives.assumption_of_mem (by simp [Γ])
    have hPredicate :
        Derives relation_domain_theory Γ predicate :=
      Derives.assumption_of_mem (by simp [Γ])
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible
            (is_relation_formula_admissible
              (set_variable_admissible 1)))
    have hCase :
        Derives relation_domain_theory
          (witnessBody :: Γ) target := by
      have hWitnessBody :
          Derives relation_domain_theory
            (witnessBody :: Γ) witnessBody :=
        Derives.assumption_of_mem (by simp)
      have hGraph :
          Derives relation_domain_theory
            (witnessBody :: Γ)
            (graph [x#1] (x#0)) :=
        Derives.conj_elim_left hWitnessBody
      have hEquality :
          Derives relation_domain_theory
            (witnessBody :: Γ)
            ((x#3) ≐ₘ (x#0)) :=
        Derives.conj_elim_right hWitnessBody
      have hSpec :
          Derives relation_domain_theory
            (witnessBody :: Γ)
            (relation_domain_spec (x#1) (x#0)) := by
        exact Derives.imp_elim
          (Derives.conj_elim_left hGraph)
          hPredicate.context_weaken_cons
      have hTransport :
          Derives relation_domain_theory
            (witnessBody :: Γ)
            (target ↔ₘ
              relation_domain_spec (x#1) (x#0)) := by
        have hRaw :=
          Metatheory.Derives.equality_iff_of_equality
          (T := relation_domain_theory)
          (Γ := witnessBody :: Γ)
          (sort := SetSort.set)
          (eigen := 0)
          (left := x#3)
          (right := x#0)
          (body := relation_domain_spec (x#1) (x#0))
          hEquality
          (hLeftCheck :=
            Term.check_certificate_of_admissible
              (set_variable_admissible 3))
          (hRightCheck :=
            Term.check_certificate_of_admissible
              (set_variable_admissible 0))
          (hBodyCheck :=
            Formula.check_certificate_of_admissible
              (relation_coordinate_spec_admissible
                (coordinate := RelationCoordinate.domain)
                (set_variable_admissible 1)
                (set_variable_admissible 0)))
        simpa [target, relation_domain_spec,
          relation_coordinate_spec,
          relation_coordinate_projection_term,
          double_union_term, Formula.substituteFree,
          Term.substituteFree, left_projection_term,
          union_term, set_variable] using hRaw
      exact Derives.iff_elim_left hTransport hSpec
    exact Derives.exists_elim
      (sort := SetSort.set)
      (eigen := 0)
      (body := witnessBody)
      (conclusion := target)
      (by
        intro formula hFormula
        rw [(relation_domain_theory_sentence
          hFormula).2]
        simp)
      (by
        intro formula hFormula
        rcases List.mem_cons.mp hFormula with
          rfl | hFormula
        · native_decide
        · rcases List.mem_singleton.mp hFormula with rfl
          native_decide)
      (by native_decide)
      (by simpa [witnessExists] using hExists)
      hCase
  ·
    let Γ : Context signature :=
      [target, predicate]
    have hTarget :
        Derives relation_domain_theory Γ target :=
      Derives.assumption_of_mem (by simp [Γ])
    have hPredicate :
        Derives relation_domain_theory Γ predicate :=
      Derives.assumption_of_mem (by simp [Γ])
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible
            (is_relation_formula_admissible
              (set_variable_admissible 1)))
    have hGraph :
        Derives relation_domain_theory Γ
          (graph [x#1] (x#3)) := by
      unfold graph
      apply Derives.conj_intro
      · apply Derives.imp_intro
          (hAntecedentCheck :=
            Formula.check_certificate_of_admissible
              (is_relation_formula_admissible
                (set_variable_admissible 1)))
        exact hTarget.context_weaken_cons
      · apply Derives.imp_intro
          (hAntecedentCheck :=
            Formula.check_certificate_of_admissible
              (Formula.Admissible.neg
                (is_relation_formula_admissible
                  (set_variable_admissible 1))))
        apply Derives.falsum_elim
          (hCheck :=
            Formula.check_certificate_of_admissible
              (Formula.Admissible.equal
                (set_variable_admissible 3)
                (set_variable_admissible 1)))
        exact Derives.neg_elim
          hPredicate.context_weaken_cons
          (Derives.assumption_of_mem
            (by simp) :
            Derives relation_domain_theory
              ((¬ₘ predicate) :: Γ)
              (¬ₘ predicate))
    have hConjunction :
        Derives relation_domain_theory Γ
          (graph [x#1] (x#3) ∧ₘ
            ((x#3) ≐ₘ (x#3))) :=
      Derives.conj_intro hGraph <|
        Derives.eq_refl_m
          (T := relation_domain_theory)
          (Γ := Γ) (x#3)
    apply Derives.exists_intro_substituted
      (eigen := 0) (witness := x#3)
    simpa [witnessBody, graph, guard,
      target, relation_domain_spec,
      relation_coordinate_spec,
      relation_coordinate_projection_term,
      double_union_term, left_projection_term,
      union_term,
      Formula.substituteFree,
      Term.substituteFree, set_variable] using hConjunction

private theorem formula_definition_instance_derives :
    Derives relation_domain_theory []
      (FunctionGraphElimination.formula data
        (domain_definition_instance (x#0) (x#1))) := by
  rw [← definition_point, formula_definition_point]
  exact compiled_definition_point_derives

private theorem formula_definition_axiom_derives :
    Derives relation_domain_theory []
      (FunctionGraphElimination.formula data
        domain_definition_axiom) := by
  have hPoint :
      Derives relation_domain_theory []
        (FunctionGraphElimination.formula data
          definition_point) := by
    rw [formula_definition_point]
    exact compiled_definition_point_derives
  have hPointAdmissible :
      Formula.Admissible definition_point :=
    domain_definition_instance_admissible
      (set_variable_admissible 0)
      (set_variable_admissible 1)
  have hCandidate :=
    graph_presentation.formula_forall_close_derives
      SetSort.set 1 definition_point
      hPointAdmissible hPoint
  have hCandidateAdmissible :
      Formula.Admissible
        (Formula.forallE SetSort.set
          (Formula.closeFreeAt SetSort.set
            1 0 definition_point)) :=
    Formula.Admissible.forall_closeFreeAt
      SetSort.set 1 hPointAdmissible
  have hRelation :=
    graph_presentation.formula_forall_close_derives
      SetSort.set 0
      (Formula.forallE SetSort.set
        (Formula.closeFreeAt SetSort.set
          1 0 definition_point))
      hCandidateAdmissible hCandidate
  simpa [domain_definition_axiom,
    definition_point] using hRelation

private theorem compile_axiom
    {source : SetFormula}
    (hSource :
      relation_domain_operator_theory source) :
    Derives relation_domain_theory []
      (FunctionGraphElimination.formula data source) := by
  rcases hSource with rfl | hSource
  · exact formula_definition_axiom_derives
  · rw [formula_base_eq hSource]
    exact Derives.theory_mem hSource
      (hFormulaCheck :=
        Formula.check_certificate_of_admissible
          (relation_domain_theory_admissible
            source hSource))

def theory_presentation :
    TheoryPresentation data where
  graph := graph_presentation
  source := relation_domain_operator_theory
  compile_axiom := compile_axiom

theorem hilbert
    {source : SetFormula}
    (hSource :
      HilbertDerives
        relation_domain_operator_theory source) :
    Derives relation_domain_theory []
      (FunctionGraphElimination.formula data source) :=
  theory_presentation.hilbert hSource

theorem derives
    {source : SetFormula}
    (hSource :
      Derives relation_domain_operator_theory []
        source) :
    Derives relation_domain_theory []
      (FunctionGraphElimination.formula data source) :=
  theory_presentation.derives
    SetSort.set hSource

theorem hilbert_falsum
    (hSource :
      HilbertDerives
        relation_domain_operator_theory
        Formula.falsum) :
    Derives relation_domain_theory []
      Formula.falsum :=
  theory_presentation.hilbert_falsum hSource

theorem derives_falsum
    (hSource :
      Derives relation_domain_operator_theory []
        Formula.falsum) :
    Derives relation_domain_theory []
      Formula.falsum :=
  theory_presentation.derives_falsum
    SetSort.set hSource

theorem consistent
    (hBase :
      Derives.Consistent
        relation_domain_theory []) :
    Derives.Consistent
      relation_domain_operator_theory [] :=
  theory_presentation.consistent
    SetSort.set hBase

theorem hilbert_consistent
    (hBase :
      Derives.Consistent
        relation_domain_theory []) :
    ¬ HilbertDerives
        relation_domain_operator_theory
        Formula.falsum :=
  theory_presentation.hilbert_consistent hBase

end RelationDomain
end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
