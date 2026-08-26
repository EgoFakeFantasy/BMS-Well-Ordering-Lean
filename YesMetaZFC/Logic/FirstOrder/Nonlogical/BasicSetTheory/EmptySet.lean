import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Separation
/-!
# 空集
空集由分离模式中恒假的谓词构造。对外保留原子的 `empty_set_spec`，只在存在性
证明边界把它与具体分离实例联系起来；这样后续定理不需要反复展开分离公理的
母集参数。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-- 恒假谓词：当前元素不等于自身。 -/
def empty_predicate : SetPredicate where
  body := ¬ₘ (bₛ#0 ≐ₘ bₛ#0)
  admissible_at := by
    prove_admissible_at
/-- 一个集合没有元素的对象语言规格。参数应当是 bound-closed 项。 -/
def empty_set_spec (empty : SetTerm) : SetFormula :=
  ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ empty) ↔ₘ ¬ₘ (bₛ#0 ≐ₘ bₛ#0)
/-- 空集存在性的闭公式。 -/
def empty_set_exists : SetFormula :=
  ∃ₘ[SetSort.set],
    ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ↔ₘ ¬ₘ (bₛ#0 ≐ₘ bₛ#0)
/-- 一个集合至少含有一个元素。 -/
def set_has_member (source : SetTerm) : SetFormula :=
  ∃ₘ[SetSort.set],
    bₛ#0 ∈ₘ source
/-- 一个集合没有任何元素。 -/
def set_has_no_members (source : SetTerm) : SetFormula :=
  ∀ₘ[SetSort.set],
    ¬ₘ (bₛ#0 ∈ₘ source)
/-- 一个集合不等于空集常量。 -/
def set_nonempty_condition (source : SetTerm) : SetFormula :=
  ¬ₘ (source ≐ₘ ∅ₘ)
/-- 由恒假分离实例生成的空集理论。 -/
def empty_set_theory : SetTheory :=
  empty_predicate.separation_theory
/-- 空集描述符的开放定义实例。 -/
def empty_set_definition_instance (candidate : SetTerm) : SetFormula := (candidate ≐ₘ ∅ₘ) ↔ₘ empty_set_spec candidate
/-- 空集常量的定义公理。 -/
def empty_set_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    empty_set_definition_instance (x#0)
/-- 在空集存在理论上加入空集常量的保守定义扩张。 -/
def empty_set_symbol_theory : SetTheory :=
  Theory.insert empty_set_definition_axiom empty_set_theory
/-- 空集常量项的纯计算证书。 -/
@[term_check]
theorem empty_set_term_check :
    Term.CheckCertificate empty_set_term SetSort.set := by
  native_decide
/-- 空集常量项的 proof-layer 合法性由计算证书恢复。 -/
theorem empty_set_term_admissible :
    Term.Admissible empty_set_term SetSort.set :=
  empty_set_term_check.admissible
/-- 空集成员规格在任意 admissible 集合项处仍然 admissible。 -/
theorem empty_set_spec_admissible
    {empty : SetTerm} (hEmpty : Term.Admissible empty SetSort.set) :
    Formula.Admissible (empty_set_spec empty) := by
  prove_admissible
/-- “至少含有一个元素”在任意 admissible 集合项处仍然 admissible。 -/
theorem set_has_member_admissible
    {source : SetTerm} (hSource : Term.Admissible source SetSort.set) :
    Formula.Admissible (set_has_member source) := by
  prove_admissible
/-- “没有任何元素”在任意 admissible 集合项处仍然 admissible。 -/
theorem set_has_no_members_admissible
    {source : SetTerm} (hSource : Term.Admissible source SetSort.set) :
    Formula.Admissible (set_has_no_members source) := by
  prove_admissible
/-- 非空条件在任意 admissible 集合项处仍然 admissible。 -/
theorem set_nonempty_condition_admissible
    {source : SetTerm} (hSource : Term.Admissible source SetSort.set) :
    Formula.Admissible (set_nonempty_condition source) :=
  Formula.Admissible.neg <|
    Formula.Admissible.equal hSource
      empty_set_term_admissible
/-- 空集描述符的开放定义实例在 admissible 候选项处仍然 admissible。 -/
theorem empty_set_definition_instance_admissible
    {candidate : SetTerm} (hCandidate : Term.Admissible candidate SetSort.set) :
    Formula.Admissible (empty_set_definition_instance candidate) :=
  Formula.Admissible.iff (Formula.Admissible.equal hCandidate
      empty_set_term_admissible) (empty_set_spec_admissible hCandidate)
/-- 空集存在公式的纯计算证书。 -/
@[formula_check]
theorem empty_set_exists_check :
    Formula.CheckCertificate empty_set_exists := by
  native_decide
/-- 空集存在公式的 proof-layer 良构性由计算证书恢复。 -/
theorem empty_set_exists_admissible :
    Formula.Admissible empty_set_exists :=
  empty_set_exists_check.admissible
/-- 空集理论仍然 admissible。 -/
theorem empty_set_theory_admissible :
    Theory.Admissible empty_set_theory := by
  exact SetPredicate.separation_theory_admissible empty_predicate
/-- 空集常量定义公理满足公共 proof-carrying 良构性边界。 -/
theorem empty_set_definition_axiom_admissible :
    Formula.Admissible empty_set_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
/-- 空集常量定义扩张后的理论仍然 admissible。 -/
theorem empty_set_symbol_theory_admissible :
    Theory.Admissible empty_set_symbol_theory :=
  Theory.admissible_insert
    empty_set_definition_axiom_admissible
    empty_set_theory_admissible
/-- 从任意母集按恒假谓词分离，恰好得到空集规格。 -/
theorem empty_separation_spec_iff (source empty : FreeVarId) :
    ⊢ₘ
      empty_predicate.separation_spec (x#source) (x#empty) ↔ₘ
        empty_set_spec (x#empty) := by
  let separation_body : SetFormula := (bₛ#0 ∈ₘ x#empty) ↔ₘ ((bₛ#0 ∈ₘ x#source) ∧ₘ
        ¬ₘ (bₛ#0 ≐ₘ bₛ#0))
  let empty_body : SetFormula := (bₛ#0 ∈ₘ x#empty) ↔ₘ
      ¬ₘ (bₛ#0 ≐ₘ bₛ#0)
  let separation_spec : SetFormula :=
    ∀ₘ[SetSort.set], separation_body
  let empty_spec : SetFormula :=
    ∀ₘ[SetSort.set], empty_body
  let element :=
    FreshVariable.fresh_id SetSort.set
      [separation_spec, empty_spec,
        separation_body, empty_body]
  have hElementFreshSeparation : (SetSort.set, element) freshForₘ
        separation_spec := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hElementFreshEmpty : (SetSort.set, element) freshForₘ
        empty_spec := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hElementFreshSeparationBody : (SetSort.set, element) freshForₘ
        separation_body := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hElementFreshEmptyBody : (SetSort.set, element) freshForₘ
        empty_body := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hSourceAdmissible :
      Term.Admissible (x#source) SetSort.set :=
    set_variable_admissible source
  have hEmptyAdmissible :
      Term.Admissible (x#empty) SetSort.set :=
    set_variable_admissible empty
  have hElementAdmissible :
      Term.Admissible (x#element) SetSort.set :=
    set_variable_admissible element
  have hSeparationSpecAdmissible :
      Formula.Admissible separation_spec := by
    simpa [separation_spec, separation_body] using
      empty_predicate.separation_spec_admissible
        hSourceAdmissible hEmptyAdmissible
  have hEmptySpecAdmissible :
      Formula.Admissible empty_spec := by
    simpa [empty_spec] using
      empty_set_spec_admissible hEmptyAdmissible
  have hElementMemSourceAdmissible :
      Formula.Admissible (x#element ∈ₘ x#source) :=
    membership_formula_admissible
      hElementAdmissible hSourceAdmissible
  have hElementMemEmptyAdmissible :
      Formula.Admissible (x#element ∈ₘ x#empty) :=
    membership_formula_admissible
      hElementAdmissible hEmptyAdmissible
  have hElementEqualityAdmissible :
      Formula.Admissible (x#element ≐ₘ x#element) :=
    Formula.Admissible.equal
      hElementAdmissible hElementAdmissible
  have hElementNegEqualityAdmissible :
      Formula.Admissible (¬ₘ (x#element ≐ₘ x#element)) :=
    Formula.Admissible.neg hElementEqualityAdmissible
  have hElementConditionAdmissible :
      Formula.Admissible ((x#element ∈ₘ x#source) ∧ₘ
          ¬ₘ (x#element ≐ₘ x#element)) :=
    Formula.Admissible.conj
      hElementMemSourceAdmissible
      hElementNegEqualityAdmissible
  change ⊢ₘ separation_spec ↔ₘ empty_spec
  apply FirstOrder.Derives.iffIntro
  · have hUniversal :
        [separation_spec] ⊢ₘ separation_spec :=
      .assumption (by simp)
    have hOpened :=
      FirstOrder.Derives.forall_elim_fvar
        SetSort.set element separation_body hUniversal
    have hSeparationAt :
        [separation_spec] ⊢ₘ (x#element ∈ₘ x#empty) ↔ₘ ((x#element ∈ₘ x#source) ∧ₘ
              ¬ₘ (x#element ≐ₘ x#element)) := by
      simpa [separation_body, Formula.openAt,
        Term.openAt] using hOpened
    have hEmptyAt :
        [separation_spec] ⊢ₘ (x#element ∈ₘ x#empty) ↔ₘ
            ¬ₘ (x#element ≐ₘ x#element) := by
      apply FirstOrder.Derives.iffIntro
      · have hSeparationAt' :=
          FirstOrder.Derives.context_weaken_cons (assumption := x#element ∈ₘ x#empty)
            hSeparationAt
        have hCondition :=
          FirstOrder.Derives.iffElimRight
            hSeparationAt' (.assumption (by simp))
        exact FirstOrder.Derives.conjElimRight hCondition
      · have hEquality : (¬ₘ (x#element ≐ₘ x#element)) ::
                [separation_spec] ⊢ₘ
              x#element ≐ₘ x#element :=
          FirstOrder.Derives.eq_refl_m (x#element)
        have hNegEquality : (¬ₘ (x#element ≐ₘ x#element)) ::
                [separation_spec] ⊢ₘ
              ¬ₘ (x#element ≐ₘ x#element) :=
          .assumption (by simp)
        exact FirstOrder.Derives.falsumElim
          (FirstOrder.Derives.negElim hEquality hNegEquality)
    have hEmptyAtOpened :
        [separation_spec] ⊢ₘ
          Formula.openAt SetSort.set 0 (x#element) empty_body := by
      simpa [empty_body, Formula.openAt,
        Term.openAt] using hEmptyAt
    have hGeneralized :=
      FirstOrder.Derives.forall_intro (T := (Theory.empty : SetTheory)) (Γ := [separation_spec]) (sort := SetSort.set) (eigen := element) (body :=
          Formula.openAt SetSort.set 0 (x#element) empty_body) (by
          intro formula hFormula
          cases hFormula) (by
          intro formula hFormula
          rcases List.mem_singleton.mp hFormula with rfl
          exact hElementFreshSeparation)
        hEmptyAtOpened
    simpa [empty_spec,
      Formula.closeFreeAt_openAt
        SetSort.set element 0 empty_body
        hElementFreshEmptyBody] using hGeneralized
  · have hUniversal :
        [empty_spec] ⊢ₘ empty_spec :=
      .assumption (by simp)
    have hOpened :=
      FirstOrder.Derives.forall_elim_fvar
        SetSort.set element empty_body hUniversal
    have hEmptyAt :
        [empty_spec] ⊢ₘ (x#element ∈ₘ x#empty) ↔ₘ
            ¬ₘ (x#element ≐ₘ x#element) := by
      simpa [empty_body, Formula.openAt,
        Term.openAt] using hOpened
    have hSeparationAt :
        [empty_spec] ⊢ₘ (x#element ∈ₘ x#empty) ↔ₘ ((x#element ∈ₘ x#source) ∧ₘ
              ¬ₘ (x#element ≐ₘ x#element)) := by
      apply FirstOrder.Derives.iffIntro
      · have hEmptyAt' :=
          FirstOrder.Derives.context_weaken_cons (assumption := x#element ∈ₘ x#empty)
            hEmptyAt
        have hNegEquality :=
          FirstOrder.Derives.iffElimRight
            hEmptyAt' (.assumption (by simp))
        have hEquality : (x#element ∈ₘ x#empty) ::
                [empty_spec] ⊢ₘ
              x#element ≐ₘ x#element :=
          FirstOrder.Derives.eq_refl_m (x#element)
        exact FirstOrder.Derives.falsumElim
          (FirstOrder.Derives.negElim hEquality hNegEquality)
      · have hEmptyAt' :=
          FirstOrder.Derives.context_weaken_cons (assumption := (x#element ∈ₘ x#source) ∧ₘ
                ¬ₘ (x#element ≐ₘ x#element))
            hEmptyAt
        have hCondition : ((x#element ∈ₘ x#source) ∧ₘ
                ¬ₘ (x#element ≐ₘ x#element)) ::
                [empty_spec] ⊢ₘ (x#element ∈ₘ x#source) ∧ₘ
                ¬ₘ (x#element ≐ₘ x#element) :=
          .assumption (by simp)
        exact FirstOrder.Derives.iffElimLeft
          hEmptyAt' (FirstOrder.Derives.conjElimRight hCondition)
    have hSeparationAtOpened :
        [empty_spec] ⊢ₘ
          Formula.openAt SetSort.set 0 (x#element) separation_body := by
      simpa [separation_body, Formula.openAt,
        Term.openAt] using hSeparationAt
    have hGeneralized :=
      FirstOrder.Derives.forall_intro (T := (Theory.empty : SetTheory)) (Γ := [empty_spec]) (sort := SetSort.set) (eigen := element) (body :=
          Formula.openAt SetSort.set 0 (x#element) separation_body) (by
          intro formula hFormula
          cases hFormula) (by
          intro formula hFormula
          rcases List.mem_singleton.mp hFormula with rfl
          exact hElementFreshEmpty)
        hSeparationAtOpened
    simpa [separation_spec,
      Formula.closeFreeAt_openAt
        SetSort.set element 0 separation_body
        hElementFreshSeparationBody] using hGeneralized
/-- 恒假分离实例推出空集存在。 -/
theorem empty_set_exists_derives :
    ⊢ₘ[empty_set_theory] empty_set_exists := by
  let source := empty_predicate.source_parameter
  let separation_body : SetFormula :=
    ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ↔ₘ ((bₛ#0 ∈ₘ x#source) ∧ₘ
          empty_predicate.body)
  let element :=
    FreshVariable.fresh_id SetSort.set
      [separation_body, empty_set_exists]
  have hElementFreshBody : (SetSort.set, element) freshForₘ
        separation_body := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hElementFreshConclusion : (SetSort.set, element) freshForₘ
        empty_set_exists := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hSourceAdmissible :
      Term.Admissible (x#source) SetSort.set :=
    set_variable_admissible source
  have hElementAdmissible :
      Term.Admissible (x#element) SetSort.set :=
    set_variable_admissible element
  have hOpenedSeparationAdmissible :
      Formula.Admissible (Formula.openAt SetSort.set 0 (x#element) separation_body) := by
    refine Formula.Admissible.exists_openAt (σ := signature) (body := separation_body) (term := x#element)
      SetSort.set ?_ hElementAdmissible
    simpa [SetPredicate.separation_exists,
      separation_body] using
      empty_predicate.separation_exists_admissible
        hSourceAdmissible
  have hSeparation :
      ⊢ₘ[empty_set_theory]
        empty_predicate.separation_exists (x#source) :=
    SetPredicate.separation_exists_derives
      empty_predicate source
  have hSeparationClosed :
      ⊢ₘ[empty_set_theory] (∃ₘ[SetSort.set, element],
          Formula.openAt SetSort.set 0 (x#element) separation_body) := by
    simpa [SetPredicate.separation_exists,
      separation_body,
      Formula.closeFreeAt_openAt
        SetSort.set element 0 separation_body
        hElementFreshBody] using hSeparation
  have hCaseImp :
      ⊢ₘ
        Formula.openAt SetSort.set 0 (x#element) separation_body ⟶ₘ
          empty_set_exists := by
    nd_apply FirstOrder.Derives.impIntro
    have hOpened :
        [Formula.openAt SetSort.set 0 (x#element) separation_body] ⊢ₘ
            Formula.openAt SetSort.set 0 (x#element) separation_body :=
      .assumption (by simp)
    have hSeparationSpec :
        [Formula.openAt SetSort.set 0 (x#element) separation_body] ⊢ₘ
            empty_predicate.separation_spec (x#source) (x#element) := by
      simpa [separation_body,
        SetPredicate.separation_spec,
        empty_predicate, Formula.openAt,
        Formula.next_depth, Term.openAt] using hOpened
    have hBridge :
        [Formula.openAt SetSort.set 0 (x#element) separation_body] ⊢ₘ
            empty_predicate.separation_spec (x#source) (x#element) ↔ₘ
              empty_set_spec (x#element) :=
      FirstOrder.Derives.context_weaken_cons (empty_separation_spec_iff source element)
    have hEmptySpec :=
      FirstOrder.Derives.iffElimRight
        hBridge hSeparationSpec
    nd_apply FirstOrder.Derives.exists_intro
      (term := x#element)
    simpa [empty_set_spec, Formula.openAt,
      Formula.next_depth, Term.openAt] using hEmptySpec
  have hExistsImp :
      ⊢ₘ[empty_set_theory] (∃ₘ[SetSort.set, element],
          Formula.openAt SetSort.set 0 (x#element) separation_body) ⟶ₘ
          empty_set_exists :=
    Metatheory.Derives.exists_imp_of_theorem (T := empty_set_theory) (Γ := []) (sort := SetSort.set) (eigen := element) (body :=
        Formula.openAt SetSort.set 0 (x#element) separation_body) (conclusion := empty_set_exists)
      hElementFreshConclusion hCaseImp
  exact FirstOrder.Derives.impElim
    hExistsImp hSeparationClosed
/-- 两个满足空集规格的集合相等。 -/
theorem empty_set_unique (left right : FreeVarId) :
    ⊢ₘ[extensionality_theory]
      empty_set_spec (x#left) ⟶ₘ
        empty_set_spec (x#right) ⟶ₘ (x#left ≐ₘ x#right) := by
  simpa [empty_set_spec,
    membership_specification] using
    membership_specification_unique (x#left) (x#right) (¬ₘ (bₛ#0 ≐ₘ bₛ#0)) (set_variable_admissible left) (set_variable_admissible right)
      (empty_set_spec_admissible (set_variable_admissible left)) (empty_set_spec_admissible (set_variable_admissible right))
/-- 空集常量定义公理可在任意 admissible 集合项处实例化。 -/
theorem empty_set_definition_instance_derives (candidate : SetTerm) (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[empty_set_symbol_theory]
      empty_set_definition_instance candidate := by
  have hAxiom :
      ⊢ₘ[empty_set_symbol_theory]
        empty_set_definition_axiom :=
    FirstOrder.Derives.theory_mem (by
      exact Or.inl rfl)
  have hInstance :=
    FirstOrder.Derives.forall_elim
      (term := candidate) hAxiom
  simpa [empty_set_definition_axiom,
    empty_set_definition_instance,
    empty_set_spec,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.substituteFree, Term.substituteFree] using hInstance
/-- 定义扩张中的空集常量满足空集规格。 -/
theorem empty_set_term_spec_derives :
    ⊢ₘ[empty_set_symbol_theory]
      empty_set_spec ∅ₘ := by
  have hDefinition :=
    empty_set_definition_instance_derives
      empty_set_term empty_set_term_admissible
  exact FirstOrder.Derives.iffElimRight hDefinition
    (FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set) empty_set_term)
/-- 任意满足空集规格的 admissible 集合项都等于空集常量。 -/
theorem empty_set_eq_term_of_spec (candidate : SetTerm) (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[empty_set_symbol_theory]
      empty_set_spec candidate ⟶ₘ (candidate ≐ₘ ∅ₘ) := by
  have hSpecification :
      Formula.Admissible (empty_set_spec candidate) :=
    empty_set_spec_admissible hCandidate
  nd_apply FirstOrder.Derives.impIntro
  have hDefinition :
      empty_set_spec candidate ::
          [] ⊢ₘ[empty_set_symbol_theory]
        empty_set_definition_instance candidate :=
    FirstOrder.Derives.context_weaken_cons (empty_set_definition_instance_derives
        candidate hCandidate)
  exact FirstOrder.Derives.iffElimLeft hDefinition
    (.assumption (by simp))
/-- 满足空集规格的集合不含任何元素。 -/
theorem empty_set_has_no_members (empty : FreeVarId) :
    ⊢ₘ
      empty_set_spec (x#empty) ⟶ₘ
        set_has_no_members (x#empty) := by
  let empty_spec := empty_set_spec (x#empty)
  let no_member_body : SetFormula :=
    ¬ₘ (bₛ#0 ∈ₘ x#empty)
  let element :=
    FreshVariable.fresh_id SetSort.set
      [empty_spec, no_member_body]
  have hElementFreshSpec : (SetSort.set, element) freshForₘ
        empty_spec := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hElementFreshBody : (SetSort.set, element) freshForₘ
        no_member_body := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hEmptyAdmissible :
      Term.Admissible (x#empty) SetSort.set :=
    set_variable_admissible empty
  have hEmptySpecAdmissible :
      Formula.Admissible empty_spec := by
    simpa [empty_spec] using
      empty_set_spec_admissible hEmptyAdmissible
  have hElementAdmissible :
      Term.Admissible (x#element) SetSort.set :=
    set_variable_admissible element
  have hElementMemEmptyAdmissible :
      Formula.Admissible (x#element ∈ₘ x#empty) :=
    membership_formula_admissible
      hElementAdmissible hEmptyAdmissible
  change ⊢ₘ empty_spec ⟶ₘ (∀ₘ[SetSort.set], no_member_body)
  nd_apply FirstOrder.Derives.impIntro
  have hUniversal :
      [empty_spec] ⊢ₘ empty_spec :=
    .assumption (by simp)
  have hOpened :=
    FirstOrder.Derives.forall_elim_fvar
      SetSort.set element ((bₛ#0 ∈ₘ x#empty) ↔ₘ
        ¬ₘ (bₛ#0 ≐ₘ bₛ#0))
      hUniversal
  have hEmptyAt :
      [empty_spec] ⊢ₘ (x#element ∈ₘ x#empty) ↔ₘ
          ¬ₘ (x#element ≐ₘ x#element) := by
    simpa [empty_spec, empty_set_spec,
      Formula.openAt, Term.openAt] using hOpened
  have hNoMemberAt :
      [empty_spec] ⊢ₘ
        ¬ₘ (x#element ∈ₘ x#empty) := by
    nd_apply FirstOrder.Derives.negIntro
    have hEmptyAt' :=
      FirstOrder.Derives.context_weaken_cons (assumption := x#element ∈ₘ x#empty)
        hEmptyAt
    have hNegEquality :=
      FirstOrder.Derives.iffElimRight
        hEmptyAt' (.assumption (by simp))
    have hEquality : (x#element ∈ₘ x#empty) ::
            [empty_spec] ⊢ₘ
          x#element ≐ₘ x#element :=
      FirstOrder.Derives.eq_refl_m (x#element)
    exact FirstOrder.Derives.negElim
      hEquality hNegEquality
  have hNoMemberAtOpened :
      [empty_spec] ⊢ₘ
        Formula.openAt SetSort.set 0 (x#element) no_member_body := by
    simpa [no_member_body, Formula.openAt,
      Term.openAt] using hNoMemberAt
  have hGeneralized :=
    FirstOrder.Derives.forall_intro (T := (Theory.empty : SetTheory)) (Γ := [empty_spec]) (sort := SetSort.set) (eigen := element) (body :=
        Formula.openAt SetSort.set 0 (x#element) no_member_body) (by
        intro formula hFormula
        cases hFormula) (by
        intro formula hFormula
        rcases List.mem_singleton.mp hFormula with rfl
        exact hElementFreshSpec)
      hNoMemberAtOpened
  simpa [Formula.closeFreeAt_openAt
    SetSort.set element 0 no_member_body
    hElementFreshBody] using hGeneralized
/-- 一个集合没有元素时，它满足指向任意目标的子集成员条件。 -/
theorem no_members_implies_subset_condition (left right : FreeVarId) :
    ⊢ₘ
      set_has_no_members (x#left) ⟶ₘ
        subset_condition (x#left) (x#right) := by
  let no_members : SetFormula :=
    set_has_no_members (x#left)
  let subset_body : SetFormula := (bₛ#0 ∈ₘ x#left) ⟶ₘ (bₛ#0 ∈ₘ x#right)
  let element :=
    FreshVariable.fresh_id SetSort.set
      [no_members, subset_body]
  have hElementFreshNoMembers : (SetSort.set, element) freshForₘ
        no_members := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hElementFreshBody : (SetSort.set, element) freshForₘ
        subset_body := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hLeftAdmissible :
      Term.Admissible (x#left) SetSort.set :=
    set_variable_admissible left
  have hRightAdmissible :
      Term.Admissible (x#right) SetSort.set :=
    set_variable_admissible right
  have hElementAdmissible :
      Term.Admissible (x#element) SetSort.set :=
    set_variable_admissible element
  have hNoMembersAdmissible :
      Formula.Admissible no_members := by
    simpa [no_members] using
      set_has_no_members_admissible
        hLeftAdmissible
  have hElementMemLeftAdmissible :
      Formula.Admissible (x#element ∈ₘ x#left) :=
    membership_formula_admissible
      hElementAdmissible hLeftAdmissible
  have hElementMemRightAdmissible :
      Formula.Admissible (x#element ∈ₘ x#right) :=
    membership_formula_admissible
      hElementAdmissible hRightAdmissible
  change ⊢ₘ no_members ⟶ₘ (∀ₘ[SetSort.set], subset_body)
  nd_apply FirstOrder.Derives.impIntro
  have hUniversal :
      [no_members] ⊢ₘ no_members :=
    .assumption (by simp)
  have hOpened :=
    FirstOrder.Derives.forall_elim_fvar
      SetSort.set element (¬ₘ (bₛ#0 ∈ₘ x#left))
      hUniversal
  have hNoLeftAt :
      [no_members] ⊢ₘ
        ¬ₘ (x#element ∈ₘ x#left) := by
    simpa [no_members, Formula.openAt,
      Term.openAt] using hOpened
  have hSubsetAt :
      [no_members] ⊢ₘ (x#element ∈ₘ x#left) ⟶ₘ (x#element ∈ₘ x#right) := by
    nd_apply FirstOrder.Derives.impIntro
    have hNoLeftAt' :=
      FirstOrder.Derives.context_weaken_cons (assumption := x#element ∈ₘ x#left)
        hNoLeftAt
    have hLeft : (x#element ∈ₘ x#left) ::
            [no_members] ⊢ₘ
          x#element ∈ₘ x#left :=
      .assumption (by simp)
    exact FirstOrder.Derives.falsumElim
      (FirstOrder.Derives.negElim hLeft hNoLeftAt')
  have hSubsetAtOpened :
      [no_members] ⊢ₘ
        Formula.openAt SetSort.set 0 (x#element) subset_body := by
    simpa [subset_body, Formula.openAt,
      Term.openAt] using hSubsetAt
  have hGeneralized :=
    FirstOrder.Derives.forall_intro (T := (Theory.empty : SetTheory)) (Γ := [no_members]) (sort := SetSort.set) (eigen := element) (body :=
        Formula.openAt SetSort.set 0 (x#element) subset_body) (by
        intro formula hFormula
        cases hFormula) (by
        intro formula hFormula
        rcases List.mem_singleton.mp hFormula with rfl
        exact hElementFreshNoMembers)
      hSubsetAtOpened
  simpa [subset_condition,
    Formula.closeFreeAt_openAt
      SetSort.set element 0 subset_body
      hElementFreshBody] using hGeneralized
/-- 任意满足空集规格的集合都是每个集合的子集。 -/
theorem empty_set_subset (empty set : FreeVarId) :
    ⊢ₘ[subset_theory]
      empty_set_spec (x#empty) ⟶ₘ (x#empty ⊆ₘ x#set) := by
  let empty_spec := empty_set_spec (x#empty)
  let no_members : SetFormula :=
    set_has_no_members (x#empty)
  have hEmptySpecAdmissible :
      Formula.Admissible empty_spec := by
    simpa [empty_spec] using
      empty_set_spec_admissible (set_variable_admissible empty)
  nd_apply FirstOrder.Derives.impIntro
  have hEmpty :
      [empty_spec] ⊢ₘ[subset_theory]
        empty_spec :=
    .assumption (by simp)
  have hNoMembersImp :
      [empty_spec] ⊢ₘ[subset_theory]
        empty_spec ⟶ₘ no_members := by
    apply FirstOrder.Derives.of_empty
    simpa [empty_spec, no_members] using
      empty_set_has_no_members empty
  have hNoMembers :=
    FirstOrder.Derives.impElim
      hNoMembersImp hEmpty
  have hConditionImp :
      [empty_spec] ⊢ₘ[subset_theory]
        no_members ⟶ₘ
          subset_condition (x#empty) (x#set) := by
    apply FirstOrder.Derives.of_empty
    simpa [no_members] using
      no_members_implies_subset_condition empty set
  have hCondition :=
    FirstOrder.Derives.impElim
      hConditionImp hNoMembers
  have hDefinition :
      [empty_spec] ⊢ₘ[subset_theory]
        subset_definition_instance (x#empty) (x#set) :=
    FirstOrder.Derives.context_weaken_cons (subset_definition_instance_derives empty set)
  exact FirstOrder.Derives.iffElimLeft
    hDefinition hCondition
/-- 空集常量不含任何 admissible 元素。 -/
theorem empty_set_term_has_no_members (element : SetTerm) (hElement : Term.Admissible element SetSort.set) :
    ⊢ₘ[empty_set_symbol_theory]
      ¬ₘ (element ∈ₘ ∅ₘ) := by
  nd_apply FirstOrder.Derives.negIntro
  have hSpec : (element ∈ₘ ∅ₘ) :: []
        ⊢ₘ[empty_set_symbol_theory]
          empty_set_spec ∅ₘ :=
    FirstOrder.Derives.context_weaken_cons
      empty_set_term_spec_derives
  have hAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := element) hSpec
  have hAt : (element ∈ₘ ∅ₘ) :: []
        ⊢ₘ[empty_set_symbol_theory] (element ∈ₘ ∅ₘ) ↔ₘ
            ¬ₘ (element ≐ₘ element) := by
    simpa [empty_set_spec, Formula.openAt,
      Term.openAt, empty_set_term] using hAtRaw
  have hNegEquality :=
    FirstOrder.Derives.iffElimRight
      hAt (.assumption (by simp))
  exact FirstOrder.Derives.negElim
    (FirstOrder.Derives.eq_refl_m element)
    hNegEquality
/-- 任意已知元素都见证其所属集合非空。 -/
theorem member_implies_set_nonempty (element source : SetTerm) (hElement : Term.Admissible element SetSort.set) (hSource : Term.Admissible source SetSort.set) :
    ⊢ₘ[empty_set_symbol_theory] (element ∈ₘ source) ⟶ₘ
        set_nonempty_condition source := by
  let parameter :=
    FreshVariable.fresh_id SetSort.set
      [element ≐ₘ element]
  let body : SetFormula :=
    element ∈ₘ x#parameter
  have hParameterFreshElement : (SetSort.set, parameter) ∉
        Term.freeSupport element := by
    dsimp [parameter]
    exact FreshVariable.fresh_term_not_mem_m
      SetSort.set element
  have hElementFixedSource :
      Term.substituteFree SetSort.set
          parameter source element =
        element :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter source element
      hParameterFreshElement
  have hElementFixedEmpty :
      Term.substituteFree SetSort.set
          parameter ∅ₘ element =
        element :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter ∅ₘ element
      hParameterFreshElement
  have hMembershipSourceAdmissible :
      Formula.Admissible (element ∈ₘ source) :=
    membership_formula_admissible
      hElement hSource
  have hSourceEmptyEqualityAdmissible :
      Formula.Admissible (source ≐ₘ ∅ₘ) :=
    Formula.Admissible.equal
      hSource empty_set_term_admissible
  have hBodyAdmissible :
      Formula.Admissible body := by
    dsimp [body]
    exact membership_formula_admissible
      hElement (set_variable_admissible parameter)
  nd_apply FirstOrder.Derives.impIntro
  unfold set_nonempty_condition
  nd_apply FirstOrder.Derives.negIntro
  have hMembership : (source ≐ₘ ∅ₘ) :: (element ∈ₘ source) :: []
        ⊢ₘ[empty_set_symbol_theory]
          element ∈ₘ source :=
    .assumption (by simp)
  have hEquality : (source ≐ₘ ∅ₘ) :: (element ∈ₘ source) :: []
        ⊢ₘ[empty_set_symbol_theory]
          source ≐ₘ ∅ₘ :=
    .assumption (by simp)
  have hMembershipInstance : (source ≐ₘ ∅ₘ) :: (element ∈ₘ source) :: []
        ⊢ₘ[empty_set_symbol_theory]
          body⟪SetSort.set, parameter ↦ source⟫ₘ := by
    simpa [body, Formula.substituteFree,
      Term.substituteFree, hElementFixedSource,
      set_variable] using hMembership
  have hMembershipEmpty :=
    FirstOrder.Derives.eq_subst_m (T := empty_set_symbol_theory) (Γ :=
        [(source ≐ₘ ∅ₘ), (element ∈ₘ source)]) (sort := SetSort.set) (eigen := parameter) (left := source) (right := ∅ₘ) (body := body)
      hEquality hMembershipInstance
  have hMembershipEmptyNormalized : (source ≐ₘ ∅ₘ) :: (element ∈ₘ source) :: []
        ⊢ₘ[empty_set_symbol_theory]
          element ∈ₘ ∅ₘ := by
    simpa [body, Formula.substituteFree,
      Term.substituteFree, hElementFixedEmpty,
      set_variable] using hMembershipEmpty
  have hNoEmptyMembership : (source ≐ₘ ∅ₘ) :: (element ∈ₘ source) :: []
        ⊢ₘ[empty_set_symbol_theory]
          ¬ₘ (element ∈ₘ ∅ₘ) :=
    FirstOrder.Derives.context_weaken_cons (assumption := source ≐ₘ ∅ₘ) <|
      FirstOrder.Derives.context_weaken_cons (assumption := element ∈ₘ source) <|
        empty_set_term_has_no_members
          element hElement
  exact FirstOrder.Derives.negElim
    hMembershipEmptyNormalized hNoEmptyMembership
/-- 若不存在元素，则该集合满足空集的成员规格。 -/
theorem not_set_has_member_implies_empty_set_spec (source : SetTerm) (hSource : Term.Admissible source SetSort.set) :
    ⊢ₘ (¬ₘ set_has_member source) ⟶ₘ
        empty_set_spec source := by
  let no_member := ¬ₘ set_has_member source
  let empty_body : SetFormula := (bₛ#0 ∈ₘ source) ↔ₘ
      ¬ₘ (bₛ#0 ≐ₘ bₛ#0)
  let element :=
    FreshVariable.fresh_id SetSort.set
      [no_member, empty_body]
  have hElementFreshNoMember : (SetSort.set, element) freshForₘ
        no_member := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hElementFreshBody : (SetSort.set, element) freshForₘ
        empty_body := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hSourceOpen :
      Term.openAt SetSort.set 0 (x#element) source =
        source :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#element) source hSource.2
  have hHasMemberAdmissible :
      Formula.Admissible (set_has_member source) :=
    set_has_member_admissible hSource
  have hNoMemberAdmissible :
      Formula.Admissible no_member := by
    dsimp [no_member]
    exact Formula.Admissible.neg
      hHasMemberAdmissible
  have hElementAdmissible :
      Term.Admissible (x#element) SetSort.set :=
    set_variable_admissible element
  have hElementMembershipAdmissible :
      Formula.Admissible (x#element ∈ₘ source) :=
    membership_formula_admissible
      hElementAdmissible hSource
  have hElementEqualityAdmissible :
      Formula.Admissible (x#element ≐ₘ x#element) :=
    Formula.Admissible.equal
      hElementAdmissible hElementAdmissible
  have hElementNegEqualityAdmissible :
      Formula.Admissible (¬ₘ (x#element ≐ₘ x#element)) :=
    Formula.Admissible.neg
      hElementEqualityAdmissible
  change ⊢ₘ no_member ⟶ₘ (∀ₘ[SetSort.set], empty_body)
  nd_apply FirstOrder.Derives.impIntro
  have hAt :
      [no_member] ⊢ₘ (x#element ∈ₘ source) ↔ₘ
          ¬ₘ (x#element ≐ₘ x#element) := by
    apply FirstOrder.Derives.iffIntro
    · nd_apply FirstOrder.Derives.negIntro
      have hMembership : (x#element ≐ₘ x#element) :: (x#element ∈ₘ source) ::
                [no_member] ⊢ₘ
            x#element ∈ₘ source :=
        .assumption (by simp)
      have hExists : (x#element ≐ₘ x#element) :: (x#element ∈ₘ source) ::
                [no_member] ⊢ₘ
            set_has_member source := by
        unfold set_has_member
        nd_apply FirstOrder.Derives.exists_intro
          (term := x#element)
        simpa [Formula.openAt, Term.openAt,
          hSourceOpen] using hMembership
      have hNoMember : (x#element ≐ₘ x#element) :: (x#element ∈ₘ source) ::
                [no_member] ⊢ₘ
            ¬ₘ set_has_member source :=
        .assumption (by simp [no_member])
      exact FirstOrder.Derives.negElim
        hExists hNoMember
    · have hNegEquality : (¬ₘ (x#element ≐ₘ x#element)) ::
              [no_member] ⊢ₘ
            ¬ₘ (x#element ≐ₘ x#element) :=
        .assumption (by simp)
      have hEquality : (¬ₘ (x#element ≐ₘ x#element)) ::
              [no_member] ⊢ₘ
            x#element ≐ₘ x#element :=
        FirstOrder.Derives.eq_refl_m (x#element)
      exact FirstOrder.Derives.falsumElim
        (FirstOrder.Derives.negElim hEquality hNegEquality)
  have hAtOpened :
      [no_member] ⊢ₘ
        Formula.openAt SetSort.set 0 (x#element) empty_body := by
    simpa [empty_body, Formula.openAt,
      Term.openAt, hSourceOpen] using hAt
  have hGeneralized :=
    FirstOrder.Derives.forall_intro (T := (Theory.empty : SetTheory)) (Γ := [no_member]) (sort := SetSort.set) (eigen := element) (body :=
        Formula.openAt SetSort.set 0 (x#element) empty_body) (by
        intro formula hFormula
        cases hFormula) (by
        intro formula hFormula
        rcases List.mem_singleton.mp hFormula with rfl
        exact hElementFreshNoMember)
      hAtOpened
  simpa [empty_set_spec,
    Formula.closeFreeAt_openAt
      SetSort.set element 0 empty_body
      hElementFreshBody] using hGeneralized
/-- 不存在元素的 admissible 集合等于空集常量。 -/
theorem not_set_has_member_implies_eq_empty (source : SetTerm) (hSource : Term.Admissible source SetSort.set) :
    ⊢ₘ[empty_set_symbol_theory] (¬ₘ set_has_member source) ⟶ₘ (source ≐ₘ ∅ₘ) := by
  let no_member := ¬ₘ set_has_member source
  have hNoMemberAdmissible :
      Formula.Admissible no_member := by
    dsimp [no_member]
    exact Formula.Admissible.neg (set_has_member_admissible hSource)
  nd_apply FirstOrder.Derives.impIntro
  have hNoMember :
      [no_member] ⊢ₘ[empty_set_symbol_theory]
        no_member :=
    .assumption (by simp)
  have hSpecImp :
      [no_member] ⊢ₘ[empty_set_symbol_theory]
        no_member ⟶ₘ empty_set_spec source :=
    FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.of_empty <|
        not_set_has_member_implies_empty_set_spec
          source hSource
  have hSpec :=
    FirstOrder.Derives.impElim hSpecImp hNoMember
  have hEqImp :
      [no_member] ⊢ₘ[empty_set_symbol_theory]
        empty_set_spec source ⟶ₘ (source ≐ₘ ∅ₘ) :=
    FirstOrder.Derives.context_weaken_cons <|
      empty_set_eq_term_of_spec source hSource
  exact FirstOrder.Derives.impElim hEqImp hSpec
/-- 不等于空集的 admissible 集合必含有元素。 -/
theorem set_nonempty_implies_has_member (source : SetTerm) (hSource : Term.Admissible source SetSort.set) :
    ⊢ₘ[empty_set_symbol_theory]
      set_nonempty_condition source ⟶ₘ
        set_has_member source := by
  let nonempty := set_nonempty_condition source
  let has_member := set_has_member source
  change
    ⊢ₘ[empty_set_symbol_theory]
      nonempty ⟶ₘ has_member
  have hNonemptyAdmissible :
      Formula.Admissible nonempty := by
    dsimp [nonempty]
    exact set_nonempty_condition_admissible
      hSource
  have hHasMemberAdmissible :
      Formula.Admissible has_member := by
    dsimp [has_member]
    exact set_has_member_admissible hSource
  have hNoMemberAdmissible :
      Formula.Admissible (¬ₘ has_member) :=
    Formula.Admissible.neg
      hHasMemberAdmissible
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.byContradiction
  have hNoMember : (¬ₘ has_member) :: [nonempty]
        ⊢ₘ[empty_set_symbol_theory]
          ¬ₘ has_member :=
    .assumption (by simp)
  have hEqImp : (¬ₘ has_member) :: [nonempty]
        ⊢ₘ[empty_set_symbol_theory] (¬ₘ has_member) ⟶ₘ (source ≐ₘ ∅ₘ) :=
    FirstOrder.Derives.context_weaken_cons (assumption := ¬ₘ has_member) <|
      FirstOrder.Derives.context_weaken_cons (assumption := nonempty) <|
        by
          simpa [has_member] using
            not_set_has_member_implies_eq_empty
              source hSource
  have hEquality :=
    FirstOrder.Derives.impElim hEqImp hNoMember
  have hNonempty : (¬ₘ has_member) :: [nonempty]
        ⊢ₘ[empty_set_symbol_theory]
          ¬ₘ (source ≐ₘ ∅ₘ) := by
    simpa [nonempty, set_nonempty_condition] using (show (¬ₘ has_member) :: [nonempty]
          ⊢ₘ[empty_set_symbol_theory] nonempty from
        .assumption (by simp))
  exact FirstOrder.Derives.negElim
    hEquality hNonempty
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
