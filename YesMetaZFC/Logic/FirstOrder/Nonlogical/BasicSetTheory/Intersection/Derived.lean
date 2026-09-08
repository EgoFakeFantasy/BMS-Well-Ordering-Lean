import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Intersection.Core

/-!
# 交集派生定理

本层只保留一元交与二元交的数学接口。项、公式、作用域与新鲜变量全部由内在类型
语法表达；旧的 `Admissible`、自由变量编号、descriptor 与全称兼容包装不再进入证明。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-- 一元交定义公理的直接候选图接口。 -/
theorem intersection_eq_iff_spec
    {free : SetContext} {Γ : Context signature free}
    (family candidate : SetOpenTerm free) :
    Γ ⊢ₘ[intersection_operator_theory]
      set_nonempty_condition family ⟶ₘ
        ((candidate ≐ₘ ⋂ₘ family) ↔ₘ
          intersection_spec family candidate) := by
  simpa [intersection_definition_instance] using
    (intersection_definition_instance_derives
      (Γ := Γ) family candidate)

/-- 非空族的一元交项满足直接成员规格。 -/
theorem intersection_term_spec_derives
    {free : SetContext} {Γ : Context signature free}
    (family : SetOpenTerm free) :
    Γ ⊢ₘ[intersection_operator_theory]
      set_nonempty_condition family ⟶ₘ
        intersection_spec family (⋂ₘ family) := by
  apply FirstOrder.Derives.imp_intro
  have hDefinition := FirstOrder.Derives.context_weaken_cons
    (assumption := set_nonempty_condition family)
    (intersection_eq_iff_spec (Γ := Γ) family (⋂ₘ family))
  have hSpecification := FirstOrder.Derives.imp_elim hDefinition
    (FirstOrder.Derives.assumption List.mem_cons_self)
  exact FirstOrder.Derives.iff_elim_left hSpecification
    (Metatheory.Derives.equality_refl
      (T := intersection_operator_theory)
      (Γ := set_nonempty_condition family :: Γ) (⋂ₘ family))

/-- 已证明的集合等式可直接提升为一元交函数项等式。 -/
theorem intersection_term_congr_of_equality
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free)
    (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T] (⋂ₘ left) ≐ₘ (⋂ₘ right) := by
  let context : SetTerm [SetSort.set] free :=
    ⋂ₘ (.bvar .here : SetTerm [SetSort.set] free)
  simpa [context] using!
    (Metatheory.Derives.term_context_congr_of_equality
      (T := T) (Γ := Γ) context hEquality)

/-- 一元交函数项保持任意已证明的参数等式。 -/
theorem intersection_term_congr
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      (left ≐ₘ right) ⟶ₘ ((⋂ₘ left) ≐ₘ (⋂ₘ right)) := by
  apply FirstOrder.Derives.imp_intro
  exact intersection_term_congr_of_equality left right
    (FirstOrder.Derives.assumption List.mem_cons_self)

/-- 源集合等式可运输一元交中的成员事实。 -/
theorem intersection_membership_transport_of_equality
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (element left right : SetOpenTerm free)
    (hEquality : Γ ⊢ₘ[T] left ≐ₘ right)
    (hMembership : Γ ⊢ₘ[T] element ∈ₘ ⋂ₘ left) :
    Γ ⊢ₘ[T] element ∈ₘ ⋂ₘ right := by
  have hIntersectionEquality :=
    intersection_term_congr_of_equality left right hEquality
  exact FirstOrder.Derives.iff_elim_left
    (membership_right_iff_of_equality
      element (⋂ₘ left) (⋂ₘ right) hIntersectionEquality)
    hMembership

/-- 源集合等式运输一元交成员关系的蕴含形式。 -/
theorem intersection_membership_transport
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (left right element : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      (left ≐ₘ right) ⟶ₘ
        ((element ∈ₘ ⋂ₘ left) ⟶ₘ
          (element ∈ₘ ⋂ₘ right)) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  exact intersection_membership_transport_of_equality element left right
    (FirstOrder.Derives.assumption (by simp))
    (FirstOrder.Derives.assumption List.mem_cons_self)

/-- 等价源集合可运输同一个候选对象的一元交等式。 -/
theorem intersection_eq_transport
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (left right candidate : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      (left ≐ₘ right) ⟶ₘ
        ((candidate ≐ₘ ⋂ₘ left) ⟶ₘ
          (candidate ≐ₘ ⋂ₘ right)) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  exact Metatheory.Derives.equality_trans
    (FirstOrder.Derives.assumption List.mem_cons_self)
    (intersection_term_congr_of_equality left right
      (FirstOrder.Derives.assumption (by simp)))

/-- 规范无序对包含其左参数。 -/
theorem unordered_pair_left_mem_derives
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[pairing_operator_theory] left ∈ₘ {left, right}ₘ := by
  have hSpecification :=
    unordered_pair_term_spec_derives (Γ := Γ) left right
  have hAt := pair_spec_membership_iff
    left right {left, right}ₘ left hSpecification
  exact FirstOrder.Derives.iff_elim_right hAt
    (FirstOrder.Derives.disj_intro_left
      (Metatheory.Derives.equality_refl
        (T := pairing_operator_theory) (Γ := Γ) left))

/-- 规范无序对包含其右参数。 -/
theorem unordered_pair_right_mem_derives
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[pairing_operator_theory] right ∈ₘ {left, right}ₘ := by
  have hSpecification :=
    unordered_pair_term_spec_derives (Γ := Γ) left right
  have hAt := pair_spec_membership_iff
    left right {left, right}ₘ right hSpecification
  exact FirstOrder.Derives.iff_elim_right hAt
    (FirstOrder.Derives.disj_intro_right
      (Metatheory.Derives.equality_refl
        (T := pairing_operator_theory) (Γ := Γ) right))

/-- 规范无序对不等于空集。 -/
theorem unordered_pair_term_nonempty
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[binary_intersection_base_theory]
      set_nonempty_condition {left, right}ₘ := by
  have hMember := FirstOrder.Derives.theory_weaken
    pairing_operator_theory_subset_binary_intersection_base_theory
    (unordered_pair_left_mem_derives (Γ := Γ) left right)
  have hEmptySubset :
      ∀ {sentence : SetSentence}, empty_set_symbol_theory sentence →
        binary_intersection_base_theory sentence := by
    intro sentence hSentence
    exact Or.inr
      (intersection_base_theory_subset_intersection_operator_theory
        (empty_set_symbol_theory_subset_intersection_base_theory hSentence))
  have hNonempty :
      Γ ⊢ₘ[binary_intersection_base_theory]
        (left ∈ₘ {left, right}ₘ) ⟶ₘ
          set_nonempty_condition {left, right}ₘ :=
    FirstOrder.Derives.theory_weaken hEmptySubset
      (member_implies_set_nonempty (Γ := Γ) left {left, right}ₘ)
  exact FirstOrder.Derives.imp_elim hNonempty hMember

/-- 二元交函数项按定义等于对应无序对的一元交。 -/
theorem binary_intersection_term_eq_intersection_pair_derives
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[binary_intersection_operator_theory]
      (left ∩ₘ right) ≐ₘ (⋂ₘ {left, right}ₘ) := by
  simpa [binary_intersection_definition_instance] using
    (binary_intersection_definition_instance_derives
      (Γ := Γ) left right)

/-- 配对规格把“属于每个配对成员”化为同时属于两个端点。 -/
theorem pair_common_member_condition_iff
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (left right pair element : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      pair_spec left right pair ⟶ₘ
        (intersection_member_condition pair element ↔ₘ
          ((element ∈ₘ left) ∧ₘ (element ∈ₘ right))) := by
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free := pair_spec left right pair :: Γ
  have hPair : Δ ⊢ₘ[T] pair_spec left right pair :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hLeftPair : Δ ⊢ₘ[T] left ∈ₘ pair :=
    FirstOrder.Derives.iff_elim_right
      (pair_spec_membership_iff left right pair left hPair)
      (FirstOrder.Derives.disj_intro_left
        (Metatheory.Derives.equality_refl (T := T) (Γ := Δ) left))
  have hRightPair : Δ ⊢ₘ[T] right ∈ₘ pair :=
    FirstOrder.Derives.iff_elim_right
      (pair_spec_membership_iff left right pair right hPair)
      (FirstOrder.Derives.disj_intro_right
        (Metatheory.Derives.equality_refl (T := T) (Γ := Δ) right))
  apply FirstOrder.Derives.iff_intro
  · have hCommon :
        intersection_member_condition pair element :: Δ ⊢ₘ[T]
          intersection_member_condition pair element :=
      FirstOrder.Derives.assumption List.mem_cons_self
    have hLeft := FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.imp_elim
        (intersection_member_condition_elim
          (T := T) (Γ := intersection_member_condition pair element :: Δ)
          pair left element)
        hCommon)
      (FirstOrder.Derives.context_weaken_cons hLeftPair)
    have hRight := FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.imp_elim
        (intersection_member_condition_elim
          (T := T) (Γ := intersection_member_condition pair element :: Δ)
          pair right element)
        hCommon)
      (FirstOrder.Derives.context_weaken_cons hRightPair)
    exact FirstOrder.Derives.conj_intro hLeft hRight
  · unfold intersection_member_condition
    apply FirstOrder.Derives.forall_intro
    apply FirstOrder.Derives.imp_intro
    let member : SetOpenTerm (SetSort.set :: free) :=
      FreshVariable.newest
        (σ := signature) (free := free) SetSort.set
    let conjunction : SetOpenFormula free :=
      (element ∈ₘ left) ∧ₘ (element ∈ₘ right)
    let Θ : Context signature (SetSort.set :: free) :=
      (member ∈ₘ pair.weakenFree SetSort.set) ::
        FreshVariable.extendContext SetSort.set (conjunction :: Δ)
    change Θ ⊢ₘ[T] element.weakenFree SetSort.set ∈ₘ member
    have hPair' : Θ ⊢ₘ[T]
        pair_spec (left.weakenFree SetSort.set)
          (right.weakenFree SetSort.set)
          (pair.weakenFree SetSort.set) :=
      FirstOrder.Derives.assumption (by
        simp [Θ, Δ, conjunction, FreshVariable.extendContext])
    have hConjunction : Θ ⊢ₘ[T]
        (element.weakenFree SetSort.set ∈ₘ left.weakenFree SetSort.set) ∧ₘ
          (element.weakenFree SetSort.set ∈ₘ right.weakenFree SetSort.set) :=
      FirstOrder.Derives.assumption (by
        simp [Θ, conjunction, FreshVariable.extendContext])
    have hCases := FirstOrder.Derives.iff_elim_left
      (pair_spec_membership_iff
        (left.weakenFree SetSort.set)
        (right.weakenFree SetSort.set)
        (pair.weakenFree SetSort.set) member hPair')
      (FirstOrder.Derives.assumption List.mem_cons_self)
    apply FirstOrder.Derives.disj_elim hCases
    · have hEquality :
          (member ≐ₘ left.weakenFree SetSort.set) :: Θ ⊢ₘ[T]
            member ≐ₘ left.weakenFree SetSort.set :=
        FirstOrder.Derives.assumption List.mem_cons_self
      have hLeft := FirstOrder.Derives.conj_elim_left
        (FirstOrder.Derives.context_weaken_cons
          (assumption := member ≐ₘ left.weakenFree SetSort.set)
          hConjunction)
      exact FirstOrder.Derives.iff_elim_right
        (membership_right_iff_of_equality
          (element.weakenFree SetSort.set) member
          (left.weakenFree SetSort.set) hEquality)
        hLeft
    · have hEquality :
          (member ≐ₘ right.weakenFree SetSort.set) :: Θ ⊢ₘ[T]
            member ≐ₘ right.weakenFree SetSort.set :=
        FirstOrder.Derives.assumption List.mem_cons_self
      have hRight := FirstOrder.Derives.conj_elim_right
        (FirstOrder.Derives.context_weaken_cons
          (assumption := member ≐ₘ right.weakenFree SetSort.set)
          hConjunction)
      exact FirstOrder.Derives.iff_elim_right
        (membership_right_iff_of_equality
          (element.weakenFree SetSort.set) member
          (right.weakenFree SetSort.set) hEquality)
        hRight

/-- 配对交集规格推出对应的二元交规格。 -/
theorem pair_intersection_spec_implies_binary_intersection_spec
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (left right pair intersection : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      pair_spec left right pair ⟶ₘ
        (intersection_spec pair intersection ⟶ₘ
          binary_intersection_spec left right intersection) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  unfold binary_intersection_spec membership_specification
  apply FirstOrder.Derives.forall_intro
  let member : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest
      (σ := signature) (free := free) SetSort.set
  let Δ : Context signature free :=
    intersection_spec pair intersection :: pair_spec left right pair :: Γ
  let Θ : Context signature (SetSort.set :: free) :=
    FreshVariable.extendContext SetSort.set Δ
  have hPair : Θ ⊢ₘ[T]
      pair_spec (left.weakenFree SetSort.set)
        (right.weakenFree SetSort.set)
        (pair.weakenFree SetSort.set) :=
    FirstOrder.Derives.assumption (by
      simp [Θ, Δ, FreshVariable.extendContext])
  have hIntersection : Θ ⊢ₘ[T]
      intersection_spec (pair.weakenFree SetSort.set)
        (intersection.weakenFree SetSort.set) :=
    FirstOrder.Derives.assumption (by
      simp [Θ, Δ, FreshVariable.extendContext])
  have hAt := intersection_spec_membership_iff
    (pair.weakenFree SetSort.set)
    (intersection.weakenFree SetSort.set) member hIntersection
  have hCommon := FirstOrder.Derives.imp_elim
    (pair_common_member_condition_iff
      (T := T) (Γ := Θ)
      (left.weakenFree SetSort.set)
      (right.weakenFree SetSort.set)
      (pair.weakenFree SetSort.set) member)
    hPair
  simpa [member, Θ, Δ, FreshVariable.newest] using!
    (Metatheory.Derives.iff_trans hAt hCommon)

/-- 二元交规格的候选单孔模板在顶部实例化后直接恢复开放规格。 -/
@[simp] theorem binary_intersection_spec_instantiateTop_context
    {free : SetContext}
    (left right replacement : SetOpenTerm free) :
    (binary_intersection_spec
        (left.weakenBound SetSort.set)
        (right.weakenBound SetSort.set)
        (.bvar .here : SetTerm [SetSort.set] free)).instantiateTop replacement =
      binary_intersection_spec left right replacement := by
  unfold binary_intersection_spec
  rw [membership_specification_instantiateTop]
  rw [Term.instantiateTop_bvar_here]
  simp only [Formula.instantiateTop_conj,
    Formula.instantiateTop_rel, Arguments.instantiateTop_cons,
    Arguments.instantiateTop_nil, Term.instantiateTop_fvar,
    Term.instantiateTop_weakenBound_weakenFree]

/-- 规范二元交函数项满足直接二元成员规格。 -/
theorem binary_intersection_term_spec_derives
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[binary_intersection_operator_theory]
      binary_intersection_spec left right (left ∩ₘ right) := by
  let pair : SetOpenTerm free := {left, right}ₘ
  let intersection : SetOpenTerm free := ⋂ₘ pair
  let binary : SetOpenTerm free := left ∩ₘ right
  have hPairSpec := FirstOrder.Derives.theory_weaken
    pairing_operator_theory_subset_binary_intersection_operator_theory
    (unordered_pair_term_spec_derives (Γ := Γ) left right)
  have hPairNonempty := FirstOrder.Derives.theory_weaken
    binary_intersection_base_theory_subset_binary_intersection_operator_theory
    (unordered_pair_term_nonempty (Γ := Γ) left right)
  have hIntersectionImp := FirstOrder.Derives.theory_weaken
    intersection_operator_theory_subset_binary_intersection_operator_theory
    (intersection_term_spec_derives (Γ := Γ) pair)
  have hIntersectionSpec := FirstOrder.Derives.imp_elim
    hIntersectionImp hPairNonempty
  have hBinarySpecAtIntersection := FirstOrder.Derives.imp_elim
    (FirstOrder.Derives.imp_elim
      (pair_intersection_spec_implies_binary_intersection_spec
        (T := binary_intersection_operator_theory) (Γ := Γ)
        left right pair intersection)
      hPairSpec)
    hIntersectionSpec
  have hDefinition :=
    binary_intersection_term_eq_intersection_pair_derives
      (Γ := Γ) left right
  let body : SetFormula [SetSort.set] free :=
    binary_intersection_spec
      (left.weakenBound SetSort.set)
      (right.weakenBound SetSort.set)
      (.bvar .here : SetTerm [SetSort.set] free)
  have hTransport := Metatheory.Derives.equality_iff_of_equality
    (T := binary_intersection_operator_theory) (Γ := Γ)
    body hDefinition
  dsimp [body] at hTransport
  rw [binary_intersection_spec_instantiateTop_context,
    binary_intersection_spec_instantiateTop_context] at hTransport
  have hTransport' :
      Γ ⊢ₘ[binary_intersection_operator_theory]
        binary_intersection_spec left right binary ↔ₘ
          binary_intersection_spec left right intersection := by
    simpa [binary, intersection, pair] using hTransport
  exact FirstOrder.Derives.iff_elim_right hTransport'
    (by simpa [intersection, pair] using hBinarySpecAtIntersection)

/-- 同一二元交规格的两个候选必相等。 -/
theorem binary_intersection_unique
    {free : SetContext} {Γ : Context signature free}
    (left right first second : SetOpenTerm free) :
    Γ ⊢ₘ[extensionality_theory]
      binary_intersection_spec left right first ⟶ₘ
        (binary_intersection_spec left right second ⟶ₘ
          (first ≐ₘ second)) := by
  let element : SetOpenTerm (SetSort.set :: free) := .fvar .here
  let condition : SetOpenFormula (SetSort.set :: free) :=
    (element ∈ₘ left.weakenFree SetSort.set) ∧ₘ
      (element ∈ₘ right.weakenFree SetSort.set)
  simpa [binary_intersection_spec, condition, element] using
    (membership_specification_unique
      (Γ := Γ) first second condition)

/-- 候选项等于规范二元交，当且仅当它满足二元交规格。 -/
theorem binary_intersection_eq_iff_spec
    {free : SetContext} {Γ : Context signature free}
    (left right candidate : SetOpenTerm free) :
    Γ ⊢ₘ[binary_intersection_operator_theory]
      (candidate ≐ₘ (left ∩ₘ right)) ↔ₘ
        binary_intersection_spec left right candidate := by
  apply FirstOrder.Derives.iff_intro
  · let Δ : Context signature free :=
      (candidate ≐ₘ (left ∩ₘ right)) :: Γ
    have hEquality : Δ ⊢ₘ[binary_intersection_operator_theory]
        candidate ≐ₘ (left ∩ₘ right) :=
      FirstOrder.Derives.assumption List.mem_cons_self
    have hTermSpec := FirstOrder.Derives.context_weaken_cons
      (assumption := candidate ≐ₘ (left ∩ₘ right))
      (binary_intersection_term_spec_derives (Γ := Γ) left right)
    let body : SetFormula [SetSort.set] free :=
      binary_intersection_spec
        (left.weakenBound SetSort.set)
        (right.weakenBound SetSort.set)
        (.bvar .here : SetTerm [SetSort.set] free)
    have hTransport := Metatheory.Derives.equality_iff_of_equality
      (T := binary_intersection_operator_theory) (Γ := Δ)
      body hEquality
    dsimp [body] at hTransport
    rw [binary_intersection_spec_instantiateTop_context,
      binary_intersection_spec_instantiateTop_context] at hTransport
    have hTransport' :
        Δ ⊢ₘ[binary_intersection_operator_theory]
          binary_intersection_spec left right candidate ↔ₘ
            binary_intersection_spec left right (left ∩ₘ right) := by
      exact hTransport
    exact FirstOrder.Derives.iff_elim_right hTransport' hTermSpec
  · let Δ : Context signature free :=
      binary_intersection_spec left right candidate :: Γ
    have hCandidate : Δ ⊢ₘ[binary_intersection_operator_theory]
        binary_intersection_spec left right candidate :=
      FirstOrder.Derives.assumption List.mem_cons_self
    have hTermSpec := FirstOrder.Derives.context_weaken_cons
      (assumption := binary_intersection_spec left right candidate)
      (binary_intersection_term_spec_derives (Γ := Γ) left right)
    have hUnique := FirstOrder.Derives.theory_weaken
      extensionality_theory_subset_binary_intersection_operator_theory
      (binary_intersection_unique
        (Γ := Δ) left right candidate (left ∩ₘ right))
    exact FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.imp_elim hUnique hCandidate) hTermSpec

/-- 两组参数等式推出对应二元交函数项相等。 -/
theorem binary_intersection_term_congr_of_equalities
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (leftFirst rightFirst leftSecond rightSecond : SetOpenTerm free)
    (hFirst : Γ ⊢ₘ[T] leftFirst ≐ₘ rightFirst)
    (hSecond : Γ ⊢ₘ[T] leftSecond ≐ₘ rightSecond) :
    Γ ⊢ₘ[T]
      (leftFirst ∩ₘ leftSecond) ≐ₘ
        (rightFirst ∩ₘ rightSecond) := by
  let firstContext : SetTerm [SetSort.set] free :=
    (.bvar .here : SetTerm [SetSort.set] free) ∩ₘ
      leftSecond.weakenBound SetSort.set
  let secondContext : SetTerm [SetSort.set] free :=
    rightFirst.weakenBound SetSort.set ∩ₘ
      (.bvar .here : SetTerm [SetSort.set] free)
  have hMiddle :
      firstContext.instantiateTop rightFirst =
        secondContext.instantiateTop leftSecond := by
    change
      ((.bvar .here : SetTerm [SetSort.set] free).instantiateTop rightFirst) ∩ₘ
          ((leftSecond.weakenBound SetSort.set).instantiateTop rightFirst) =
        ((rightFirst.weakenBound SetSort.set).instantiateTop leftSecond) ∩ₘ
          ((.bvar .here : SetTerm [SetSort.set] free).instantiateTop leftSecond)
    rw [Term.instantiateTop_bvar_here,
      Term.instantiateTop_weakenBound,
      Term.instantiateTop_weakenBound,
      Term.instantiateTop_bvar_here]
  have hResult :=
    Metatheory.Derives.term_context_pair_congr_of_equalities
      (T := T) (Γ := Γ) firstContext secondContext hMiddle
      hFirst hSecond
  simpa [firstContext, secondContext] using! hResult

/-- 二元交函数项保持两组参数等式。 -/
theorem binary_intersection_term_congr
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (leftFirst rightFirst leftSecond rightSecond : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      (leftFirst ≐ₘ rightFirst) ⟶ₘ
        ((leftSecond ≐ₘ rightSecond) ⟶ₘ
          ((leftFirst ∩ₘ leftSecond) ≐ₘ
            (rightFirst ∩ₘ rightSecond))) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  exact binary_intersection_term_congr_of_equalities
    leftFirst rightFirst leftSecond rightSecond
    (FirstOrder.Derives.assumption (by simp))
    (FirstOrder.Derives.assumption List.mem_cons_self)

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
