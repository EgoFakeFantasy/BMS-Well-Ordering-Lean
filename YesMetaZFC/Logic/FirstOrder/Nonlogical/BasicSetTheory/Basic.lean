import YesMetaZFC.Logic.FirstOrder.Metatheory.Equality.Basic
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Axioms
/-!
# 基本集合论的首批具体非逻辑定理
本模块从纯逻辑中的第一存在性开始，继而建立等式与成员外延一致之间的桥，并让
外延公理、子集定义公理通过真实的非空 `Theory` 进入推演。量词实例化和等词替换
显式消费可信核接口，机械命题组合交给专用推导 tactic。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-- 第一存在性：存在一个等于自身的对象。 -/
theorem first_existence :
    ⊢ₘ (∃ₘ[SetSort.set, 0], x#0 ≐ₘ x#0) := by
  have hVariable := set_variable_admissible 0
  have hEquality :
      Formula.Admissible (x#0 ≐ₘ x#0) :=
    Formula.Admissible.equal hVariable hVariable
  have hExistential :
      Formula.Admissible (∃ₘ[SetSort.set, 0], x#0 ≐ₘ x#0) :=
    Formula.Admissible.exists_closeFreeAt
      SetSort.set 0 hEquality
  nd_apply FirstOrder.Derives.exists_intro
    (term := x#0)
  simpa [Formula.openAt_closeFreeAt
    SetSort.set 0 0 (x#0 ≐ₘ x#0)] using
      (FirstOrder.Derives.eq_refl_m
        (T := (Theory.empty : SetTheory)) (Γ := []) (x#0))
/-- 两个 free 变量相等时，它们具有完全相同的元素。 -/
theorem equality_implies_membership_agreement (left right : FreeVarId) :
    ⊢ₘ equality_to_agreement (x#left) (x#right) := by
  unfold equality_to_agreement
  have hLeft := set_variable_admissible left
  have hRight := set_variable_admissible right
  have hEqualityAdmissible :
      Formula.Admissible (x#left ≐ₘ x#right) :=
    Formula.Admissible.equal hLeft hRight
  nd_apply FirstOrder.Derives.impIntro
  let element :=
    FreshVariable.fresh_id SetSort.set
      [x#left ≐ₘ x#right]
  let parameter := element + 1
  have hElementFresh : (SetSort.set, element) ∉
        Formula.freeSupport (x#left ≐ₘ x#right) := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hElementNeLeft : element ≠ left := by
    intro hEqual
    apply hElementFresh
    rw [hEqual]
    change (SetSort.set, left) ∈
        [(SetSort.set, left), (SetSort.set, right)]
    exact by simp
  have hElementNeRight : element ≠ right := by
    intro hEqual
    apply hElementFresh
    rw [hEqual]
    change (SetSort.set, right) ∈
        [(SetSort.set, left), (SetSort.set, right)]
    exact by simp
  have hEquality :
      [x#left ≐ₘ x#right] ⊢ₘ
        x#left ≐ₘ x#right :=
    .assumption (by simp)
  have hAgreementAt :
      [x#left ≐ₘ x#right] ⊢ₘ ((x#element ∈ₘ x#left) ↔ₘ (x#element ∈ₘ x#right)) := by
    have hCongruence :=
      Metatheory.Derives.equality_iff_of_equality (T := (Theory.empty : SetTheory)) (Γ := [x#left ≐ₘ x#right]) (sort := SetSort.set) (eigen := parameter)
        (left := x#left) (right := x#right)
        (body := x#element ∈ₘ x#parameter)
        hEquality
    simpa [Formula.substituteFree, Term.substituteFree,
      parameter, set_variable] using hCongruence
  have hGeneralized :=
    FirstOrder.Derives.forall_intro (T := (Theory.empty : SetTheory)) (Γ := [x#left ≐ₘ x#right]) (sort := SetSort.set) (eigen := element) (body :=
        (x#element ∈ₘ x#left) ↔ₘ (x#element ∈ₘ x#right)) (by
        intro formula hFormula
        cases hFormula) (by
        intro formula hFormula
        rcases List.mem_singleton.mp hFormula with rfl
        exact hElementFresh)
      hAgreementAt
  simpa [membership_agreement, Formula.closeFreeAt,
    Term.closeFreeAt, set_variable, set_bound_variable,
    hElementNeLeft, hElementNeRight, Ne.symm hElementNeLeft,
    Ne.symm hElementNeRight] using hGeneralized
/--
容器等式可运输任意固定项的成员关系。
该接口直接重放 Leibniz 替换，后续关系与函数层不必为每个成员原子重复维护公式模板。
-/
theorem membership_right_iff_of_equality
    {T : SetTheory} {Γ : Context signature} (element left right : SetTerm) (hElement : Term.Admissible element SetSort.set)
    (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T] (element ∈ₘ left) ↔ₘ (element ∈ₘ right) := by
  let parameter :=
    FreshVariable.fresh_id SetSort.set
      [element ≐ₘ element]
  let body : SetFormula :=
    element ∈ₘ x#parameter
  have hElementFresh : (SetSort.set, parameter) ∉
        Term.freeSupport element := by
    dsimp [parameter]
    exact FreshVariable.fresh_term_not_mem_m
      SetSort.set element
  have hElementFixedLeft :
      Term.substituteFree SetSort.set
          parameter left element =
        element :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter left element
      hElementFresh
  have hElementFixedRight :
      Term.substituteFree SetSort.set
          parameter right element =
        element :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter right element
      hElementFresh
  have hCongruence :=
    Metatheory.Derives.equality_iff_of_equality (T := T) (Γ := Γ) (sort := SetSort.set) (eigen := parameter) (left := left) (right := right) (body := body)
      hEquality
  simpa [body, Formula.substituteFree,
    Term.substituteFree, hElementFixedLeft,
    hElementFixedRight, set_variable] using
    hCongruence
/--
元素等式可运输其在任意固定容器中的成员关系。
该接口与 `membership_right_iff_of_equality` 对称，供配对成员分类与坐标替换复用。
-/
theorem membership_left_iff_of_equality
    {T : SetTheory} {Γ : Context signature} (left right set : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hSet : Term.Admissible set SetSort.set) (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T] (left ∈ₘ set) ↔ₘ (right ∈ₘ set) := by
  let parameter :=
    FreshVariable.fresh_id SetSort.set
      [set ≐ₘ set]
  let body : SetFormula :=
    x#parameter ∈ₘ set
  have hSetFresh : (SetSort.set, parameter) ∉
        Term.freeSupport set := by
    dsimp [parameter]
    exact FreshVariable.fresh_term_not_mem_m
      SetSort.set set
  have hSetFixedLeft :
      Term.substituteFree SetSort.set
          parameter left set =
        set :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter left set
      hSetFresh
  have hSetFixedRight :
      Term.substituteFree SetSort.set
          parameter right set =
        set :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter right set
      hSetFresh
  have hCongruence :=
    Metatheory.Derives.equality_iff_of_equality (T := T) (Γ := Γ) (sort := SetSort.set) (eigen := parameter) (left := left) (right := right) (body := body)
      hEquality
  simpa [body, Formula.substituteFree,
    Term.substituteFree, hSetFixedLeft,
    hSetFixedRight, set_variable] using
    hCongruence
/--
左端集合等式可运输其与任意固定集合之间的子集关系。
该接口是 `membership_left_iff_of_equality` 在二元集合关系上的直接推广；完整理论码、
类运算与关系像的定义等式都可复用它，而不必在各自模块重复展开 Leibniz 替换。
-/
theorem subset_left_iff_of_equality
    {T : SetTheory} {Γ : Context signature} (left right set : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hSet : Term.Admissible set SetSort.set) (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T] (left ⊆ₘ set) ↔ₘ (right ⊆ₘ set) := by
  let parameter :=
    FreshVariable.fresh_id SetSort.set
      [set ≐ₘ set]
  let body : SetFormula :=
    x#parameter ⊆ₘ set
  have hSetFresh : (SetSort.set, parameter) ∉
        Term.freeSupport set := by
    dsimp [parameter]
    exact FreshVariable.fresh_term_not_mem_m
      SetSort.set set
  have hSetFixedLeft :
      Term.substituteFree SetSort.set
          parameter left set =
        set :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter left set
      hSetFresh
  have hSetFixedRight :
      Term.substituteFree SetSort.set
          parameter right set =
        set :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter right set
      hSetFresh
  have hCongruence :=
    Metatheory.Derives.equality_iff_of_equality (T := T) (Γ := Γ) (sort := SetSort.set) (eigen := parameter) (left := left) (right := right) (body := body)
      hEquality
  simpa [body, Formula.substituteFree,
    Term.substituteFree, hSetFixedLeft,
    hSetFixedRight, set_variable] using
    hCongruence
/-- 外延理论可在任意两个 admissible 集合项处实例化外延公理。 -/
theorem extensionality_instance_derives_of_admissible (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[extensionality_theory]
      extensionality_instance left right := by
  have hAxiom :
      ⊢ₘ[extensionality_theory] extensionality_axiom :=
    FirstOrder.Derives.theory_mem (by
      rfl)
  simp only [extensionality_axiom,
    Metatheory.Formula.forall_close_cons,
    Metatheory.Formula.forall_close_nil] at hAxiom
  have hLeftInstance :=
    FirstOrder.Derives.forall_elim
      (term := left) hAxiom
  have hRightInstance :=
    FirstOrder.Derives.forall_elim
      (term := right) hLeftInstance
  have hLeftOpenZero :
      Term.openAt SetSort.set 0 right left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 right left hLeft.2
  have hLeftOpenOne :
      Term.openAt SetSort.set 1 right left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 right left hLeft.2
  simpa [extensionality_axiom,
    extensionality_instance, agreement_to_equality,
    membership_agreement,
    Metatheory.Formula.forall_close,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth,
    Formula.substituteFree, Term.openAt,
    Term.closeFreeAt, Term.substituteFree,
    hLeftOpenZero, hLeftOpenOne,
    set_variable, set_bound_variable] using hRightInstance
/-- 以一个单元素 binder 描述集合的通用成员规格。 -/
def membership_specification (candidate : SetTerm) (condition : SetFormula) :
    SetFormula :=
  ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ candidate) ↔ₘ condition
/--
两个集合满足同一个成员规格时相等。
该外延性接口把“点态规格相同”与具体构造解耦，供分离、关系代数和函数图统一复用。
-/
theorem membership_specification_unique (left right : SetTerm) (condition : SetFormula) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hLeftSpecification :
      Formula.Admissible (membership_specification left condition)) (hRightSpecification :
      Formula.Admissible (membership_specification right condition)) :
    ⊢ₘ[extensionality_theory]
      membership_specification left condition ⟶ₘ
        membership_specification right condition ⟶ₘ (left ≐ₘ right) := by
  let left_spec :=
    membership_specification left condition
  let right_spec :=
    membership_specification right condition
  let agreement_body : SetFormula := (bₛ#0 ∈ₘ left) ↔ₘ (bₛ#0 ∈ₘ right)
  let element :=
    FreshVariable.fresh_id SetSort.set
      [left_spec, right_spec, agreement_body]
  have hElementFreshLeft : (SetSort.set, element) freshForₘ
        left_spec := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hElementFreshRight : (SetSort.set, element) freshForₘ
        right_spec := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hElementFreshAgreement : (SetSort.set, element) freshForₘ
        agreement_body := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hLeftOpen :
      Term.openAt SetSort.set 0 (x#element) left =
        left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#element)
      left hLeft.2
  have hRightOpen :
      Term.openAt SetSort.set 0 (x#element) right =
        right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#element)
      right hRight.2
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  have hLeftSpec :
      [right_spec, left_spec] ⊢ₘ
        left_spec :=
    .assumption (by simp)
  have hRightSpec :
      [right_spec, left_spec] ⊢ₘ
        right_spec :=
    .assumption (by simp)
  have hLeftAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := x#element) hLeftSpec
  have hRightAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := x#element) hRightSpec
  let opened_condition :=
    Formula.openAt SetSort.set 0 (x#element) condition
  have hElement := set_variable_admissible element
  have hElementMemLeft :
      Formula.Admissible (x#element ∈ₘ left) :=
    membership_formula_admissible hElement hLeft
  have hElementMemRight :
      Formula.Admissible (x#element ∈ₘ right) :=
    membership_formula_admissible hElement hRight
  have hLeftAt :
      [right_spec, left_spec] ⊢ₘ (x#element ∈ₘ left) ↔ₘ
          opened_condition := by
    simpa [left_spec, membership_specification,
      opened_condition, Formula.openAt,
      Term.openAt, hLeftOpen] using hLeftAtRaw
  have hRightAt :
      [right_spec, left_spec] ⊢ₘ (x#element ∈ₘ right) ↔ₘ
          opened_condition := by
    simpa [right_spec, membership_specification,
      opened_condition, Formula.openAt,
      Term.openAt, hRightOpen] using hRightAtRaw
  have hAgreementAt :
      [right_spec, left_spec] ⊢ₘ (x#element ∈ₘ left) ↔ₘ (x#element ∈ₘ right) := by
    apply FirstOrder.Derives.iffIntro
    · have hLeftAt' :=
        FirstOrder.Derives.context_weaken_cons (assumption := x#element ∈ₘ left)
          hLeftAt
      have hRightAt' :=
        FirstOrder.Derives.context_weaken_cons (assumption := x#element ∈ₘ left)
          hRightAt
      exact FirstOrder.Derives.iffElimLeft
          hRightAt'
            (FirstOrder.Derives.iffElimRight hLeftAt'
              (.assumption (by simp)))
    · have hLeftAt' :=
        FirstOrder.Derives.context_weaken_cons (assumption := x#element ∈ₘ right)
          hLeftAt
      have hRightAt' :=
        FirstOrder.Derives.context_weaken_cons (assumption := x#element ∈ₘ right)
          hRightAt
      exact FirstOrder.Derives.iffElimLeft
          hLeftAt'
            (FirstOrder.Derives.iffElimRight hRightAt'
              (.assumption (by simp)))
  have hAgreementAtOpened :
      [right_spec, left_spec] ⊢ₘ
        Formula.openAt SetSort.set 0 (x#element) agreement_body := by
    simpa [agreement_body, Formula.openAt,
      Term.openAt, hLeftOpen,
      hRightOpen] using hAgreementAt
  have hAgreement :
      [right_spec, left_spec] ⊢ₘ
        membership_agreement left right := by
    have hGeneralized :=
      FirstOrder.Derives.forall_intro (T := (Theory.empty : SetTheory)) (Γ := [right_spec, left_spec]) (sort := SetSort.set) (eigen := element) (body :=
          Formula.openAt SetSort.set 0 (x#element) agreement_body) (by
          intro formula hFormula
          cases hFormula) (by
          intro formula hFormula
          rcases List.mem_cons.mp hFormula with
            rfl | hFormula
          · exact hElementFreshRight
          · rcases List.mem_singleton.mp hFormula with rfl
            exact hElementFreshLeft)
        hAgreementAtOpened
    simpa [membership_agreement, agreement_body,
      Formula.closeFreeAt_openAt
        SetSort.set element 0 agreement_body
        hElementFreshAgreement] using hGeneralized
  have hAgreementInTheory :
      [right_spec, left_spec]
        ⊢ₘ[extensionality_theory]
          membership_agreement left right :=
    FirstOrder.Derives.theory_weaken (by simp [Theory.empty])
      hAgreement
  have hExtensionality :
      [right_spec, left_spec]
        ⊢ₘ[extensionality_theory]
          extensionality_instance left right :=
    FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.context_weaken_cons <|
        extensionality_instance_derives_of_admissible
          left right hLeft hRight
  exact FirstOrder.Derives.impElim
    hExtensionality hAgreementInTheory
/-- 外延理论自动提供任意两个自由变量处的外延公理实例。 -/
theorem extensionality_instance_derives (left right : FreeVarId) :
    ⊢ₘ[extensionality_theory]
      extensionality_instance (x#left) (x#right) := by
  exact extensionality_instance_derives_of_admissible (x#left) (x#right) (set_variable_admissible left) (set_variable_admissible right)
/-- 子集理论可在任意两个 admissible 集合项处实例化子集定义公理。 -/
theorem subset_definition_instance_derives_of_admissible (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[subset_theory]
      subset_definition_instance left right := by
  have hAxiom :
      ⊢ₘ[subset_theory] subset_definition_axiom :=
    FirstOrder.Derives.theory_mem (by
      exact Or.inl rfl)
  simp only [subset_definition_axiom,
    Metatheory.Formula.forall_close_cons,
    Metatheory.Formula.forall_close_nil] at hAxiom
  have hLeftInstance :=
    FirstOrder.Derives.forall_elim
      (term := left) hAxiom
  have hRightInstance :=
    FirstOrder.Derives.forall_elim
      (term := right) hLeftInstance
  have hLeftOpenZero :
      Term.openAt SetSort.set 0 right left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 right left hLeft.2
  have hLeftOpenOne :
      Term.openAt SetSort.set 1 right left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 right left hLeft.2
  simpa [subset_definition_axiom,
    subset_definition_instance, subset_condition,
    Metatheory.Formula.forall_close,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth,
    Formula.substituteFree, Term.openAt,
    Term.closeFreeAt, Term.substituteFree,
    set_variable, set_bound_variable,
    hLeftOpenZero, hLeftOpenOne] using hRightInstance
/--
若一个集合的成员规格由“属于给定母集”与额外条件合取而成，则它包含于该母集。
该接口只消费子集定义，不依赖额外条件的内部结构，供所有分离式构造复用。
-/
theorem membership_specification_subset_source (candidate source : SetTerm) (condition : SetFormula) (hCandidate : Term.Admissible candidate SetSort.set)
    (hSource : Term.Admissible source SetSort.set) (hSpecification :
      Formula.Admissible (membership_specification candidate ((bₛ#0 ∈ₘ source) ∧ₘ condition))) :
    ⊢ₘ[subset_theory]
      membership_specification candidate ((bₛ#0 ∈ₘ source) ∧ₘ condition) ⟶ₘ (candidate ⊆ₘ source) := by
  let specification :=
    membership_specification candidate ((bₛ#0 ∈ₘ source) ∧ₘ condition)
  let subset_body : SetFormula := (bₛ#0 ∈ₘ candidate) ⟶ₘ (bₛ#0 ∈ₘ source)
  let member :=
    FreshVariable.fresh_id SetSort.set
      [specification, subset_body]
  have hMemberFreshSpecification : (SetSort.set, member) freshForₘ
        specification := by
    dsimp [member]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hMemberFreshSubset : (SetSort.set, member) freshForₘ
        subset_body := by
    dsimp [member]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hCandidateOpen :
      Term.openAt SetSort.set 0 (x#member) candidate =
        candidate :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#member)
      candidate hCandidate.2
  have hSourceOpen :
      Term.openAt SetSort.set 0 (x#member) source =
        source :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#member)
      source hSource.2
  nd_apply FirstOrder.Derives.impIntro
  have hSpecification :
      [specification] ⊢ₘ[subset_theory]
        specification :=
    .assumption (by simp)
  have hAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := x#member) hSpecification
  have hAt :
      [specification] ⊢ₘ[subset_theory] (x#member ∈ₘ candidate) ↔ₘ ((x#member ∈ₘ source) ∧ₘ
            Formula.openAt SetSort.set 0 (x#member) condition) := by
    simpa [specification,
      membership_specification,
      Formula.openAt, Term.openAt,
      hCandidateOpen, hSourceOpen] using hAtRaw
  have hMemberImp :
      [specification] ⊢ₘ[subset_theory] (x#member ∈ₘ candidate) ⟶ₘ (x#member ∈ₘ source) := by
    have hMemberCandidate :
        Formula.Admissible (x#member ∈ₘ candidate) :=
      Formula.Admissible.iff_left hAt.admissible
    nd_apply FirstOrder.Derives.impIntro
    have hAt' :=
      FirstOrder.Derives.context_weaken_cons (assumption := x#member ∈ₘ candidate) hAt
    have hCondition :=
      FirstOrder.Derives.iffElimRight hAt' (.assumption (by simp))
    exact FirstOrder.Derives.conjElimLeft hCondition
  have hMemberImpOpened :
      [specification] ⊢ₘ[subset_theory]
        Formula.openAt SetSort.set 0 (x#member) subset_body := by
    simpa [subset_body, Formula.openAt,
      Term.openAt, hCandidateOpen,
      hSourceOpen] using hMemberImp
  have hSubsetCondition :
      [specification] ⊢ₘ[subset_theory]
        subset_condition candidate source := by
    have hGeneralized :=
      FirstOrder.Derives.forall_intro (T := subset_theory) (Γ := [specification]) (sort := SetSort.set) (eigen := member) (body :=
          Formula.openAt SetSort.set 0 (x#member) subset_body) (by
          intro formula hFormula
          have hSentence :=
            subset_theory_sentence hFormula
          rw [hSentence.2]
          simp) (by
          intro formula hFormula
          rcases List.mem_singleton.mp hFormula with rfl
          exact hMemberFreshSpecification)
        hMemberImpOpened
    simpa [subset_condition,
      Formula.closeFreeAt_openAt
        SetSort.set member 0 subset_body
        hMemberFreshSubset] using hGeneralized
  have hDefinition :
      [specification] ⊢ₘ[subset_theory]
        subset_definition_instance candidate source :=
    FirstOrder.Derives.context_weaken_cons (subset_definition_instance_derives_of_admissible
        candidate source hCandidate hSource)
  exact FirstOrder.Derives.iffElimLeft
    hDefinition hSubsetCondition
/-- 子集理论自动提供任意两个自由变量处的子集定义实例。 -/
theorem subset_definition_instance_derives (left right : FreeVarId) :
    ⊢ₘ[subset_theory]
      subset_definition_instance (x#left) (x#right) := by
  exact subset_definition_instance_derives_of_admissible (x#left) (x#right) (set_variable_admissible left) (set_variable_admissible right)
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
