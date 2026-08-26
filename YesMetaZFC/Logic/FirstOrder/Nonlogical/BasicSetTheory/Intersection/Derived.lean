import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Intersection.Core
/-!
# 交集描述符与派生定理
本模块建立一元交与二元交的规范项、等式运输、成员规格及全称闭包。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-- 一元交定义公理的直接候选图接口。 -/
theorem intersection_eq_iff_spec (family candidate : SetTerm) (hFamily : Term.Admissible family SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[intersection_operator_theory]
      set_nonempty_condition family ⟶ₘ ((candidate ≐ₘ ⋂ₘ family) ↔ₘ
          intersection_spec family candidate) := by
  simpa [intersection_definition_instance] using
    intersection_definition_instance_derives
      family candidate hFamily hCandidate
/-- 非空族的一元交项满足直接成员规格。 -/
theorem intersection_term_spec_derives (family : SetTerm) (hFamily : Term.Admissible family SetSort.set) :
    ⊢ₘ[intersection_operator_theory]
      set_nonempty_condition family ⟶ₘ
        intersection_spec family (⋂ₘ family) := by
  let nonempty := set_nonempty_condition family
  let intersection := intersection_term family
  let spec := intersection_spec family intersection
  have hIntersection :
      Term.Admissible intersection SetSort.set :=
    intersection_term_admissible family hFamily
  have hNonemptyAdmissible :
      Formula.Admissible nonempty := by
    dsimp [nonempty]
    exact set_nonempty_condition_admissible
      hFamily
  change
    ⊢ₘ[intersection_operator_theory]
      nonempty ⟶ₘ spec
  nd_apply FirstOrder.Derives.impIntro
  have hDefinition :
      [nonempty] ⊢ₘ[intersection_operator_theory]
        nonempty ⟶ₘ ((intersection ≐ₘ intersection) ↔ₘ spec) :=
    FirstOrder.Derives.context_weaken_cons <|
      by
        simpa [nonempty, intersection, spec] using
          intersection_eq_iff_spec
            family intersection
            hFamily hIntersection
  have hIff :=
    FirstOrder.Derives.impElim
      hDefinition (.assumption (by simp))
  exact FirstOrder.Derives.iffElimRight
    hIff (FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set) intersection)
/-- 已证明的集合等式可直接提升为一元交函数项等式。 -/
theorem intersection_term_congr_of_equality
    {T : SetTheory} {Γ : Context signature} (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T] (⋂ₘ left) ≐ₘ (⋂ₘ right) := by
  exact Metatheory.Derives.unary_term_constructor_congr_of_equality
    intersection_term
    intersection_term_admissible
    (by intros; simp [Term.substituteFree])
    left right hLeft hRight hEquality
/-- 一元交函数项保持自由集合变量的等式。 -/
theorem intersection_term_congr (left right : FreeVarId) :
    ⊢ₘ (x#left ≐ₘ x#right) ⟶ₘ ((⋂ₘ x#left) ≐ₘ (⋂ₘ x#right)) := by
  nd_apply FirstOrder.Derives.impIntro
  exact intersection_term_congr_of_equality
    (x#left) (x#right)
    (set_variable_admissible left)
    (set_variable_admissible right)
    (.assumption (by simp))
/-- 源集合等式可运输一元交中的成员事实。 -/
theorem intersection_membership_transport_of_equality
    {T : SetTheory} {Γ : Context signature} (element left right : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) (hMembership : Γ ⊢ₘ[T] element ∈ₘ ⋂ₘ left) :
    Γ ⊢ₘ[T] element ∈ₘ ⋂ₘ right := by
  let left_intersection := intersection_term left
  let right_intersection := intersection_term right
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
  have hElementFixedLeft :
      Term.substituteFree SetSort.set
          parameter left_intersection element =
        element :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter left_intersection
      element hParameterFreshElement
  have hElementFixedRight :
      Term.substituteFree SetSort.set
          parameter right_intersection element =
        element :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter right_intersection
      element hParameterFreshElement
  have hIntersectionEquality :
      Γ ⊢ₘ[T]
        left_intersection ≐ₘ right_intersection := by
    simpa [left_intersection,
      right_intersection] using
      intersection_term_congr_of_equality
        left right hLeft hRight hEquality
  have hLeftIntersection :
      Term.Admissible
        left_intersection SetSort.set :=
    intersection_term_admissible left hLeft
  have hRightIntersection :
      Term.Admissible
        right_intersection SetSort.set :=
    intersection_term_admissible right hRight
  have hTransport :=
    FirstOrder.Derives.eq_subst_m
      (T := T) (Γ := Γ) (sort := SetSort.set)
      (eigen := parameter) (left := left_intersection)
      (right := right_intersection) (body := body)
      hIntersectionEquality (by
        simpa [body, left_intersection,
          Formula.substituteFree, Term.substituteFree,
          hElementFixedLeft, set_variable] using
            hMembership)
  simpa [body, Formula.substituteFree,
    Term.substituteFree, hElementFixedLeft,
    hElementFixedRight, set_variable] using
      hTransport
/-- 文献定理 2.20(1) 的自由变量蕴含形式。 -/
theorem intersection_membership_transport (left right element : FreeVarId) :
    ⊢ₘ (x#left ≐ₘ x#right) ⟶ₘ ((x#element ∈ₘ ⋂ₘ x#left) ⟶ₘ (x#element ∈ₘ ⋂ₘ x#right)) := by
  have hLeftAdmissible :=
    set_variable_admissible left
  have hRightAdmissible :=
    set_variable_admissible right
  have hElementAdmissible :=
    set_variable_admissible element
  have hEqualityAdmissible :
      Formula.Admissible (x#left ≐ₘ x#right) :=
    Formula.Admissible.equal
      hLeftAdmissible hRightAdmissible
  have hMembershipAdmissible :
      Formula.Admissible (x#element ∈ₘ ⋂ₘ x#left) :=
    membership_formula_admissible
      hElementAdmissible (intersection_term_admissible (x#left) hLeftAdmissible)
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  exact intersection_membership_transport_of_equality (x#element) (x#left) (x#right)
    hLeftAdmissible
    hRightAdmissible
    (.assumption (by simp))
    (.assumption (by simp))
/-- 等价源集合可运输同一个候选对象的一元交等式。 -/
theorem intersection_eq_transport (left right candidate : FreeVarId) :
    ⊢ₘ (x#left ≐ₘ x#right) ⟶ₘ ((x#candidate ≐ₘ ⋂ₘ x#left) ⟶ₘ (x#candidate ≐ₘ ⋂ₘ x#right)) := by
  let left_intersection :=
    intersection_term (x#left)
  let right_intersection :=
    intersection_term (x#right)
  have hLeftIntersection :
      Term.Admissible
        left_intersection SetSort.set :=
    intersection_term_admissible (x#left) (set_variable_admissible left)
  have hRightIntersection :
      Term.Admissible
        right_intersection SetSort.set :=
    intersection_term_admissible (x#right) (set_variable_admissible right)
  have hLeftAdmissible :=
    set_variable_admissible left
  have hRightAdmissible :=
    set_variable_admissible right
  have hCandidateAdmissible :=
    set_variable_admissible candidate
  have hSourceEqualityAdmissible :
      Formula.Admissible (x#left ≐ₘ x#right) :=
    Formula.Admissible.equal
      hLeftAdmissible hRightAdmissible
  have hCandidateEqualityAdmissible :
      Formula.Admissible (x#candidate ≐ₘ left_intersection) :=
    Formula.Admissible.equal
      hCandidateAdmissible hLeftIntersection
  change
    ⊢ₘ (x#left ≐ₘ x#right) ⟶ₘ ((x#candidate ≐ₘ left_intersection) ⟶ₘ (x#candidate ≐ₘ right_intersection))
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  have hSourceEquality :
      [x#candidate ≐ₘ left_intersection,
          x#left ≐ₘ x#right] ⊢ₘ
        x#left ≐ₘ x#right :=
    .assumption (by simp)
  have hCandidateEquality :
      [x#candidate ≐ₘ left_intersection,
          x#left ≐ₘ x#right] ⊢ₘ
        x#candidate ≐ₘ left_intersection :=
    .assumption (by simp)
  have hIntersectionEquality :
      [x#candidate ≐ₘ left_intersection,
          x#left ≐ₘ x#right] ⊢ₘ
        left_intersection ≐ₘ
          right_intersection := by
    simpa [left_intersection,
      right_intersection] using
      intersection_term_congr_of_equality (T := (Theory.empty : SetTheory)) (Γ :=
          [x#candidate ≐ₘ left_intersection,
            x#left ≐ₘ x#right]) (x#left) (x#right)
        hLeftAdmissible
        hRightAdmissible
        hSourceEquality
  exact Metatheory.Derives.equality_trans
    hCandidateEquality hIntersectionEquality
/-- 无序对项包含左参数。 -/
theorem unordered_pair_left_mem_derives (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[pairing_operator_theory]
      left ∈ₘ {left, right}ₘ := by
  let pair := unordered_pair_term left right
  have hPair :
      Term.Admissible pair SetSort.set :=
    unordered_pair_term_admissible
      left right hLeft hRight
  have hSpec :
      ⊢ₘ[pairing_operator_theory]
        pair_spec left right pair := by
    simpa [pair] using
      unordered_pair_term_spec_derives
        left right hLeft hRight
  have hAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := left) hSpec
  have hLeftOpen :
      Term.openAt SetSort.set 0 left left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 left left hLeft.2
  have hRightOpen :
      Term.openAt SetSort.set 0 left right = right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 left right hRight.2
  have hPairOpen :
      Term.openAt SetSort.set 0 left pair = pair :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 left pair hPair.2
  have hAt :
      ⊢ₘ[pairing_operator_theory] (left ∈ₘ pair) ↔ₘ ((left ≐ₘ left) ∨ₘ (left ≐ₘ right)) := by
    simpa [pair_spec, pair_member_condition,
      Formula.openAt, Term.openAt,
      hLeftOpen, hRightOpen, hPairOpen] using
        hAtRaw
  have hCondition :
      ⊢ₘ[pairing_operator_theory] (left ≐ₘ left) ∨ₘ (left ≐ₘ right) :=
    FirstOrder.Derives.disjIntroLeft
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) left)
  simpa [pair] using
    FirstOrder.Derives.iffElimLeft
      hAt hCondition
/-- 无序对项包含右参数。 -/
theorem unordered_pair_right_mem_derives (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[pairing_operator_theory]
      right ∈ₘ {left, right}ₘ := by
  let pair := unordered_pair_term left right
  have hPair :
      Term.Admissible pair SetSort.set :=
    unordered_pair_term_admissible
      left right hLeft hRight
  have hSpec :
      ⊢ₘ[pairing_operator_theory]
        pair_spec left right pair := by
    simpa [pair] using
      unordered_pair_term_spec_derives
        left right hLeft hRight
  have hAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := right) hSpec
  have hLeftOpen :
      Term.openAt SetSort.set 0 right left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 right left hLeft.2
  have hRightOpen :
      Term.openAt SetSort.set 0 right right = right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 right right hRight.2
  have hPairOpen :
      Term.openAt SetSort.set 0 right pair = pair :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 right pair hPair.2
  have hAt :
      ⊢ₘ[pairing_operator_theory] (right ∈ₘ pair) ↔ₘ ((right ≐ₘ left) ∨ₘ (right ≐ₘ right)) := by
    simpa [pair_spec, pair_member_condition,
      Formula.openAt, Term.openAt,
      hLeftOpen, hRightOpen, hPairOpen] using
        hAtRaw
  have hCondition :
      ⊢ₘ[pairing_operator_theory] (right ≐ₘ left) ∨ₘ (right ≐ₘ right) :=
    FirstOrder.Derives.disjIntroRight
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) right)
  simpa [pair] using
    FirstOrder.Derives.iffElimLeft
      hAt hCondition
/-- 任意无序对项都不等于空集。 -/
theorem unordered_pair_term_nonempty (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[binary_intersection_base_theory]
      set_nonempty_condition {left, right}ₘ := by
  let pair := unordered_pair_term left right
  have hPair :
      Term.Admissible pair SetSort.set :=
    unordered_pair_term_admissible
      left right hLeft hRight
  have hMember :
      ⊢ₘ[binary_intersection_base_theory]
        left ∈ₘ pair :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        pairing_operator_theory_subset_binary_intersection_base_theory
          hFormula) (by
        simpa [pair] using
          unordered_pair_left_mem_derives
            left right hLeft hRight)
  have hNonemptyImp :
      ⊢ₘ[binary_intersection_base_theory] (left ∈ₘ pair) ⟶ₘ
          set_nonempty_condition pair :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        empty_set_symbol_theory_subset_binary_intersection_base_theory
          hFormula) (member_implies_set_nonempty
        left pair hLeft hPair)
  simpa [pair] using
    FirstOrder.Derives.impElim
      hNonemptyImp hMember
/-- 二元交项等于对应无序对的一元交。 -/
theorem binary_intersection_term_eq_intersection_pair_derives (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[binary_intersection_operator_theory] (left ∩ₘ right) ≐ₘ (⋂ₘ {left, right}ₘ) := by
  simpa [binary_intersection_definition_instance] using
    binary_intersection_definition_instance_derives
      left right hLeft hRight
/-- 二元交候选图与文献描述符等价。 -/
theorem binary_intersection_eq_iff_descriptor (left right candidate : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[binary_intersection_operator_theory] (candidate ≐ₘ (left ∩ₘ right)) ↔ₘ
        binary_intersection_descriptor
          left right candidate := by
  let pair := unordered_pair_term left right
  let intersection := intersection_term pair
  let binary :=
    binary_intersection_term left right
  have hPair :
      Term.Admissible pair SetSort.set :=
    unordered_pair_term_admissible
      left right hLeft hRight
  have hIntersection :
      Term.Admissible intersection SetSort.set :=
    intersection_term_admissible pair hPair
  have hBinary :
      Term.Admissible binary SetSort.set :=
    binary_intersection_term_admissible
      left right hLeft hRight
  have hCandidateBinaryAdmissible :
      Formula.Admissible (candidate ≐ₘ binary) :=
    Formula.Admissible.equal
      hCandidate hBinary
  have hCandidateIntersectionAdmissible :
      Formula.Admissible (candidate ≐ₘ intersection) :=
    Formula.Admissible.equal
      hCandidate hIntersection
  have hDefinition :
      ⊢ₘ[binary_intersection_operator_theory]
        binary ≐ₘ intersection := by
    simpa [binary, intersection, pair] using
      binary_intersection_term_eq_intersection_pair_derives
        left right hLeft hRight
  change
    ⊢ₘ[binary_intersection_operator_theory] (candidate ≐ₘ binary) ↔ₘ (candidate ≐ₘ intersection)
  apply FirstOrder.Derives.iffIntro
  · have hCandidateBinary : (candidate ≐ₘ binary) :: []
          ⊢ₘ[binary_intersection_operator_theory]
            candidate ≐ₘ binary :=
      .assumption (by simp)
    have hDefinition' : (candidate ≐ₘ binary) :: []
          ⊢ₘ[binary_intersection_operator_theory]
            binary ≐ₘ intersection :=
      FirstOrder.Derives.context_weaken_cons
        hDefinition
    exact Metatheory.Derives.equality_trans
      hCandidateBinary hDefinition'
  · have hCandidateIntersection : (candidate ≐ₘ intersection) :: []
          ⊢ₘ[binary_intersection_operator_theory]
            candidate ≐ₘ intersection :=
      .assumption (by simp)
    have hIntersectionBinary : (candidate ≐ₘ intersection) :: []
          ⊢ₘ[binary_intersection_operator_theory]
            intersection ≐ₘ binary :=
      Metatheory.Derives.equality_symm
        (FirstOrder.Derives.context_weaken_cons hDefinition)
    exact Metatheory.Derives.equality_trans
      hCandidateIntersection hIntersectionBinary
/-- 二元交项满足文献中的“对无序对取交”描述。 -/
theorem binary_intersection_term_descriptor_derives (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[binary_intersection_operator_theory]
      binary_intersection_descriptor
        left right (left ∩ₘ right) :=
  FirstOrder.Derives.iffElimRight (binary_intersection_eq_iff_descriptor
      left right (left ∩ₘ right)
      hLeft hRight (binary_intersection_term_admissible
        left right hLeft hRight))
    (FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set) (left ∩ₘ right))
/-- 对配对的每个成员成立，等价于分别对左右参数成立。 -/
theorem pair_common_member_condition_iff (left right pair element : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hPair : Term.Admissible pair SetSort.set) (hElement : Term.Admissible element SetSort.set) :
    ⊢ₘ
      pair_spec left right pair ⟶ₘ (pair_common_member_condition pair element ↔ₘ ((element ∈ₘ left) ∧ₘ (element ∈ₘ right))) := by
  let pair_formula := pair_spec left right pair
  let common :=
    pair_common_member_condition pair element
  let conjunction : SetFormula := (element ∈ₘ left) ∧ₘ (element ∈ₘ right)
  let member_body : SetFormula := (bₛ#0 ∈ₘ pair) ⟶ₘ (element ∈ₘ bₛ#0)
  let member :=
    FreshVariable.fresh_id SetSort.set
      [pair_formula, common, conjunction,
        member_body]
  let member_mem : SetFormula :=
    x#member ∈ₘ pair
  let left_equality : SetFormula :=
    x#member ≐ₘ left
  let right_equality : SetFormula :=
    x#member ≐ₘ right
  let parameter :=
    FreshVariable.fresh_id SetSort.set
      [element ≐ₘ element]
  let membership_body : SetFormula :=
    element ∈ₘ x#parameter
  have hMemberFreshPair : (SetSort.set, member) freshForₘ
        pair_formula := by
    dsimp [member]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hMemberFreshConjunction : (SetSort.set, member) freshForₘ
        conjunction := by
    dsimp [member]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hMemberFreshBody : (SetSort.set, member) freshForₘ
        member_body := by
    dsimp [member]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hParameterFreshElement : (SetSort.set, parameter) ∉
        Term.freeSupport element := by
    dsimp [parameter]
    exact FreshVariable.fresh_term_not_mem_m
      SetSort.set element
  have hElementFixedMember :
      Term.substituteFree SetSort.set
          parameter (x#member) element =
        element :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter (x#member) element
      hParameterFreshElement
  have hElementFixedLeft :
      Term.substituteFree SetSort.set
          parameter left element =
        element :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter left element
      hParameterFreshElement
  have hElementFixedRight :
      Term.substituteFree SetSort.set
          parameter right element =
        element :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter right element
      hParameterFreshElement
  have hPairOpenLeft :
      Term.openAt SetSort.set 0 left pair = pair :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 left pair hPair.2
  have hPairOpenRight :
      Term.openAt SetSort.set 0 right pair = pair :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 right pair hPair.2
  have hPairOpenMember :
      Term.openAt SetSort.set 0 (x#member) pair =
        pair :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#member) pair hPair.2
  have hLeftOpenLeft :
      Term.openAt SetSort.set 0 left left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 left left hLeft.2
  have hLeftOpenRight :
      Term.openAt SetSort.set 0 right left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 right left hLeft.2
  have hLeftOpenMember :
      Term.openAt SetSort.set 0 (x#member) left =
        left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#member) left hLeft.2
  have hRightOpenLeft :
      Term.openAt SetSort.set 0 left right = right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 left right hRight.2
  have hRightOpenRight :
      Term.openAt SetSort.set 0 right right = right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 right right hRight.2
  have hRightOpenMember :
      Term.openAt SetSort.set 0 (x#member) right =
        right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#member) right hRight.2
  have hElementOpenLeft :
      Term.openAt SetSort.set 0 left element = element :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 left element hElement.2
  have hElementOpenRight :
      Term.openAt SetSort.set 0 right element = element :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 right element hElement.2
  have hElementOpenMember :
      Term.openAt SetSort.set 0 (x#member) element =
        element :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#member) element hElement.2
  have hPairFormulaAdmissible :
      Formula.Admissible pair_formula := by
    dsimp [pair_formula]
    exact pair_spec_admissible
      hLeft hRight hPair
  have hCommonAdmissible :
      Formula.Admissible common := by
    dsimp [common]
    exact pair_common_member_condition_admissible
      hPair hElement
  have hConjunctionAdmissible :
      Formula.Admissible conjunction := by
    dsimp [conjunction]
    exact Formula.Admissible.conj (membership_formula_admissible
        hElement hLeft) (membership_formula_admissible
        hElement hRight)
  have hMemberAdmissible :
      Term.Admissible (x#member) SetSort.set :=
    set_variable_admissible member
  have hMemberMemAdmissible :
      Formula.Admissible member_mem := by
    dsimp [member_mem]
    exact membership_formula_admissible
      hMemberAdmissible hPair
  have hLeftEqualityAdmissible :
      Formula.Admissible left_equality := by
    dsimp [left_equality]
    exact Formula.Admissible.equal
      hMemberAdmissible hLeft
  have hRightEqualityAdmissible :
      Formula.Admissible right_equality := by
    dsimp [right_equality]
    exact Formula.Admissible.equal
      hMemberAdmissible hRight
  change
    ⊢ₘ pair_formula ⟶ₘ (common ↔ₘ conjunction)
  nd_apply FirstOrder.Derives.impIntro
  apply FirstOrder.Derives.iffIntro
  · have hPairSpec :
        common :: [pair_formula] ⊢ₘ
          pair_formula :=
      .assumption (by simp)
    have hCommon :
        common :: [pair_formula] ⊢ₘ
          common :=
      .assumption (by simp)
    have hPairAtLeftRaw :=
      FirstOrder.Derives.forall_elim
        (term := left) hPairSpec
    have hPairAtLeft :
        common :: [pair_formula] ⊢ₘ (left ∈ₘ pair) ↔ₘ ((left ≐ₘ left) ∨ₘ (left ≐ₘ right)) := by
      simpa [pair_formula, pair_spec,
        pair_member_condition,
        Formula.openAt, Term.openAt,
        hPairOpenLeft, hLeftOpenLeft,
        hRightOpenLeft] using hPairAtLeftRaw
    have hPairAtRightRaw :=
      FirstOrder.Derives.forall_elim
        (term := right) hPairSpec
    have hPairAtRight :
        common :: [pair_formula] ⊢ₘ (right ∈ₘ pair) ↔ₘ ((right ≐ₘ left) ∨ₘ (right ≐ₘ right)) := by
      simpa [pair_formula, pair_spec,
        pair_member_condition,
        Formula.openAt, Term.openAt,
        hPairOpenRight, hLeftOpenRight,
        hRightOpenRight] using hPairAtRightRaw
    have hLeftMemPair :=
      FirstOrder.Derives.iffElimLeft
        hPairAtLeft (FirstOrder.Derives.disjIntroLeft
          (FirstOrder.Derives.eq_refl_m
            (sort := SetSort.set) left))
    have hRightMemPair :=
      FirstOrder.Derives.iffElimLeft
        hPairAtRight (FirstOrder.Derives.disjIntroRight
          (FirstOrder.Derives.eq_refl_m
            (sort := SetSort.set) right))
    have hCommonAtLeftRaw :=
      FirstOrder.Derives.forall_elim
        (term := left) hCommon
    have hCommonAtLeft :
        common :: [pair_formula] ⊢ₘ (left ∈ₘ pair) ⟶ₘ (element ∈ₘ left) := by
      simpa [common,
        pair_common_member_condition,
        Formula.openAt, Term.openAt,
        hPairOpenLeft, hElementOpenLeft] using
          hCommonAtLeftRaw
    have hCommonAtRightRaw :=
      FirstOrder.Derives.forall_elim
        (term := right) hCommon
    have hCommonAtRight :
        common :: [pair_formula] ⊢ₘ (right ∈ₘ pair) ⟶ₘ (element ∈ₘ right) := by
      simpa [common,
        pair_common_member_condition,
        Formula.openAt, Term.openAt,
        hPairOpenRight, hElementOpenRight] using
          hCommonAtRightRaw
    exact FirstOrder.Derives.conjIntro (FirstOrder.Derives.impElim
        hCommonAtLeft hLeftMemPair) (FirstOrder.Derives.impElim
        hCommonAtRight hRightMemPair)
  · have hPairSpec :
        conjunction :: [pair_formula] ⊢ₘ
          pair_formula :=
      .assumption (by simp)
    have hConjunction :
        conjunction :: [pair_formula] ⊢ₘ
          conjunction :=
      .assumption (by simp)
    have hElementLeft :=
      FirstOrder.Derives.conjElimLeft
        hConjunction
    have hElementRight :=
      FirstOrder.Derives.conjElimRight
        hConjunction
    have hPairAtMemberRaw :=
      FirstOrder.Derives.forall_elim
        (term := x#member) hPairSpec
    have hPairAtMember :
        conjunction :: [pair_formula] ⊢ₘ
          member_mem ↔ₘ (left_equality ∨ₘ right_equality) := by
      simpa [pair_formula, pair_spec,
        pair_member_condition, member_mem,
        left_equality, right_equality,
        Formula.openAt, Term.openAt,
        hPairOpenMember, hLeftOpenMember,
        hRightOpenMember] using hPairAtMemberRaw
    have hMemberImp :
        conjunction :: [pair_formula] ⊢ₘ
          member_mem ⟶ₘ (element ∈ₘ x#member) := by
      nd_apply FirstOrder.Derives.impIntro
      have hPairAtMember' :=
        FirstOrder.Derives.context_weaken_cons (assumption := member_mem)
          hPairAtMember
      have hDisjunction :=
        FirstOrder.Derives.iffElimRight
          hPairAtMember' (.assumption (by simp [member_mem])
            )
      have hLeftCase :
          left_equality :: member_mem ::
              conjunction :: [pair_formula] ⊢ₘ
            element ∈ₘ x#member := by
        have hEquality :
            left_equality :: member_mem ::
                conjunction :: [pair_formula] ⊢ₘ
              x#member ≐ₘ left := by
          simpa [left_equality] using (show
              left_equality :: member_mem ::
                  conjunction :: [pair_formula] ⊢ₘ
                left_equality from
              .assumption (by simp)
                )
        have hIff :=
          Metatheory.Derives.equality_iff_of_equality (T := (Theory.empty : SetTheory)) (Γ :=
              [left_equality, member_mem,
                conjunction, pair_formula]) (sort := SetSort.set) (eigen := parameter) (left := x#member) (right := left) (body := membership_body)
            hEquality
        have hIffNormalized :
            left_equality :: member_mem ::
                conjunction :: [pair_formula] ⊢ₘ (element ∈ₘ x#member) ↔ₘ (element ∈ₘ left) := by
          simpa [membership_body,
            Formula.substituteFree,
            Term.substituteFree,
            hElementFixedMember,
            hElementFixedLeft,
            set_variable] using hIff
        have hElementLeft' :
            left_equality :: member_mem ::
                conjunction :: [pair_formula] ⊢ₘ
              element ∈ₘ left :=
          FirstOrder.Derives.context_weaken_cons (assumption := left_equality) <|
            FirstOrder.Derives.context_weaken_cons (assumption := member_mem)
              hElementLeft
        exact FirstOrder.Derives.iffElimLeft
          hIffNormalized hElementLeft'
      have hRightCase :
          right_equality :: member_mem ::
              conjunction :: [pair_formula] ⊢ₘ
            element ∈ₘ x#member := by
        have hEquality :
            right_equality :: member_mem ::
                conjunction :: [pair_formula] ⊢ₘ
              x#member ≐ₘ right := by
          simpa [right_equality] using (show
              right_equality :: member_mem ::
                  conjunction :: [pair_formula] ⊢ₘ
                right_equality from
              .assumption (by simp)
                )
        have hIff :=
          Metatheory.Derives.equality_iff_of_equality (T := (Theory.empty : SetTheory)) (Γ :=
              [right_equality, member_mem,
                conjunction, pair_formula]) (sort := SetSort.set) (eigen := parameter) (left := x#member) (right := right) (body := membership_body)
            hEquality
        have hIffNormalized :
            right_equality :: member_mem ::
                conjunction :: [pair_formula] ⊢ₘ (element ∈ₘ x#member) ↔ₘ (element ∈ₘ right) := by
          simpa [membership_body,
            Formula.substituteFree,
            Term.substituteFree,
            hElementFixedMember,
            hElementFixedRight,
            set_variable] using hIff
        have hElementRight' :
            right_equality :: member_mem ::
                conjunction :: [pair_formula] ⊢ₘ
              element ∈ₘ right :=
          FirstOrder.Derives.context_weaken_cons (assumption := right_equality) <|
            FirstOrder.Derives.context_weaken_cons (assumption := member_mem)
              hElementRight
        exact FirstOrder.Derives.iffElimLeft
          hIffNormalized hElementRight'
      exact FirstOrder.Derives.disjElim
        hDisjunction hLeftCase hRightCase
    have hMemberImpOpened :
        conjunction :: [pair_formula] ⊢ₘ
          Formula.openAt SetSort.set 0 (x#member) member_body := by
      simpa [member_body, member_mem,
        Formula.openAt, Term.openAt,
        hPairOpenMember,
        hElementOpenMember] using hMemberImp
    have hGeneralized :=
      FirstOrder.Derives.forall_intro (T := (Theory.empty : SetTheory)) (Γ := [conjunction, pair_formula]) (sort := SetSort.set) (eigen := member) (body :=
          Formula.openAt SetSort.set 0 (x#member) member_body) (by
          intro formula hFormula
          cases hFormula) (by
          intro formula hFormula
          rcases List.mem_cons.mp hFormula with rfl | hFormula
          · exact hMemberFreshConjunction
          · rcases List.mem_singleton.mp hFormula with rfl
            exact hMemberFreshPair)
        hMemberImpOpened
    simpa [common,
      pair_common_member_condition,
      Formula.closeFreeAt_openAt
        SetSort.set member 0 member_body
        hMemberFreshBody] using hGeneralized
/-- 配对规格与一元交规格组合成二元交的成员合取规格。 -/
theorem pair_intersection_spec_implies_binary_intersection_spec (left right pair intersection : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hPair : Term.Admissible pair SetSort.set) (hIntersection : Term.Admissible intersection SetSort.set) :
    ⊢ₘ
      pair_spec left right pair ⟶ₘ (intersection_spec pair intersection ⟶ₘ
          binary_intersection_spec
            left right intersection) := by
  let pair_formula := pair_spec left right pair
  let intersection_formula :=
    intersection_spec pair intersection
  let result_body : SetFormula := (bₛ#0 ∈ₘ intersection) ↔ₘ ((bₛ#0 ∈ₘ left) ∧ₘ (bₛ#0 ∈ₘ right))
  let element :=
    FreshVariable.fresh_id SetSort.set
      [pair_formula, intersection_formula,
        result_body]
  let common_at :=
    pair_common_member_condition
      pair (x#element)
  let conjunction_at : SetFormula := (x#element ∈ₘ left) ∧ₘ (x#element ∈ₘ right)
  have hElementFreshPair : (SetSort.set, element) freshForₘ
        pair_formula := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hElementFreshIntersection : (SetSort.set, element) freshForₘ
        intersection_formula := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hElementFreshResultBody : (SetSort.set, element) freshForₘ
        result_body := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hPairOpenOne :
      Term.openAt SetSort.set 1 (x#element) pair =
        pair :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 (x#element) pair hPair.2
  have hIntersectionOpen :
      Term.openAt SetSort.set 0 (x#element) intersection =
        intersection :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#element)
      intersection hIntersection.2
  have hLeftOpen :
      Term.openAt SetSort.set 0 (x#element) left =
        left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#element) left hLeft.2
  have hRightOpen :
      Term.openAt SetSort.set 0 (x#element) right =
        right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#element) right hRight.2
  have hPairFormulaAdmissible :
      Formula.Admissible pair_formula := by
    dsimp [pair_formula]
    exact pair_spec_admissible
      hLeft hRight hPair
  have hIntersectionFormulaAdmissible :
      Formula.Admissible intersection_formula := by
    dsimp [intersection_formula]
    exact intersection_spec_admissible
      hPair hIntersection
  have hElementAdmissible :
      Term.Admissible (x#element) SetSort.set :=
    set_variable_admissible element
  have hElementMemIntersectionAdmissible :
      Formula.Admissible (x#element ∈ₘ intersection) :=
    membership_formula_admissible
      hElementAdmissible hIntersection
  have hCommonAtAdmissible :
      Formula.Admissible common_at := by
    dsimp [common_at]
    exact pair_common_member_condition_admissible
      hPair hElementAdmissible
  have hConjunctionAtAdmissible :
      Formula.Admissible conjunction_at := by
    dsimp [conjunction_at]
    exact Formula.Admissible.conj (membership_formula_admissible
        hElementAdmissible hLeft) (membership_formula_admissible
        hElementAdmissible hRight)
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  have hPairFormula :
      intersection_formula :: [pair_formula] ⊢ₘ
        pair_formula :=
    .assumption (by simp)
  have hIntersectionFormula :
      intersection_formula :: [pair_formula] ⊢ₘ
        intersection_formula :=
    .assumption (by simp)
  have hIntersectionAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := x#element) hIntersectionFormula
  have hIntersectionAt :
      intersection_formula :: [pair_formula] ⊢ₘ (x#element ∈ₘ intersection) ↔ₘ
          common_at := by
    simpa [intersection_formula,
      intersection_spec, common_at,
      pair_common_member_condition,
      Formula.openAt, Formula.next_depth,
      Term.openAt, hPairOpenOne,
      hIntersectionOpen] using
        hIntersectionAtRaw
  have hPairCommonImp :
      intersection_formula :: [pair_formula] ⊢ₘ
        pair_formula ⟶ₘ (common_at ↔ₘ conjunction_at) :=
    FirstOrder.Derives.context_weaken_cons (assumption := intersection_formula) <|
      FirstOrder.Derives.context_weaken_cons (assumption := pair_formula) <|
        by
          simpa [pair_formula, common_at,
            conjunction_at] using
            pair_common_member_condition_iff
              left right pair (x#element)
              hLeft hRight hPair (set_variable_admissible element)
  have hPairCommon :=
    FirstOrder.Derives.impElim
      hPairCommonImp hPairFormula
  have hResultAt :
      intersection_formula :: [pair_formula] ⊢ₘ (x#element ∈ₘ intersection) ↔ₘ
          conjunction_at := by
    apply FirstOrder.Derives.iffIntro
    · have hIntersectionAt' :=
        FirstOrder.Derives.context_weaken_cons (assumption := x#element ∈ₘ intersection)
          hIntersectionAt
      have hPairCommon' :=
        FirstOrder.Derives.context_weaken_cons (assumption := x#element ∈ₘ intersection)
          hPairCommon
      have hCommon :=
        FirstOrder.Derives.iffElimRight
          hIntersectionAt' (.assumption (by simp)
            )
      exact FirstOrder.Derives.iffElimRight
        hPairCommon' hCommon
    · have hIntersectionAt' :=
        FirstOrder.Derives.context_weaken_cons (assumption := conjunction_at)
          hIntersectionAt
      have hPairCommon' :=
        FirstOrder.Derives.context_weaken_cons (assumption := conjunction_at)
          hPairCommon
      have hCommon :=
        FirstOrder.Derives.iffElimLeft
          hPairCommon' (.assumption (by simp [conjunction_at])
            )
      exact FirstOrder.Derives.iffElimLeft
        hIntersectionAt' hCommon
  have hResultAtOpened :
      intersection_formula :: [pair_formula] ⊢ₘ
        Formula.openAt SetSort.set 0 (x#element) result_body := by
    simpa [result_body, conjunction_at,
      Formula.openAt, Term.openAt,
      hIntersectionOpen, hLeftOpen,
      hRightOpen] using hResultAt
  have hGeneralized :=
    FirstOrder.Derives.forall_intro (T := (Theory.empty : SetTheory)) (Γ := [intersection_formula, pair_formula]) (sort := SetSort.set) (eigen := element)
      (body :=
        Formula.openAt SetSort.set 0 (x#element) result_body) (by
        intro formula hFormula
        cases hFormula) (by
        intro formula hFormula
        rcases List.mem_cons.mp hFormula with rfl | hFormula
        · exact hElementFreshIntersection
        · rcases List.mem_singleton.mp hFormula with rfl
          exact hElementFreshPair)
      hResultAtOpened
  simpa [binary_intersection_spec,
    Formula.closeFreeAt_openAt
      SetSort.set element 0 result_body
      hElementFreshResultBody] using hGeneralized
/-- 定义扩张中的二元交项满足成员合取规格。 -/
theorem binary_intersection_term_spec_derives (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[binary_intersection_operator_theory]
      binary_intersection_spec
        left right (left ∩ₘ right) := by
  let pair := unordered_pair_term left right
  let binary :=
    binary_intersection_term left right
  have hPair :
      Term.Admissible pair SetSort.set :=
    unordered_pair_term_admissible
      left right hLeft hRight
  have hBinary :
      Term.Admissible binary SetSort.set :=
    binary_intersection_term_admissible
      left right hLeft hRight
  have hPairSpec :
      ⊢ₘ[binary_intersection_operator_theory]
        pair_spec left right pair :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        pairing_operator_theory_subset_binary_intersection_operator_theory
          hFormula) (by
        simpa [pair] using
          unordered_pair_term_spec_derives
            left right hLeft hRight)
  have hPairNonempty :
      ⊢ₘ[binary_intersection_operator_theory]
        set_nonempty_condition pair :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        binary_intersection_base_theory_subset_binary_intersection_operator_theory
          hFormula) (by
        simpa [pair] using
          unordered_pair_term_nonempty
            left right hLeft hRight)
  have hIntersectionEqSpec :
      ⊢ₘ[binary_intersection_operator_theory]
        set_nonempty_condition pair ⟶ₘ ((binary ≐ₘ ⋂ₘ pair) ↔ₘ
            intersection_spec pair binary) :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        intersection_operator_theory_subset_binary_intersection_operator_theory
          hFormula) (intersection_eq_iff_spec
        pair binary hPair hBinary)
  have hDefinition :
      ⊢ₘ[binary_intersection_operator_theory]
        binary ≐ₘ ⋂ₘ pair := by
    simpa [binary, pair] using
      binary_intersection_term_eq_intersection_pair_derives
        left right hLeft hRight
  have hIntersectionIff :=
    FirstOrder.Derives.impElim
      hIntersectionEqSpec hPairNonempty
  have hIntersectionSpec :=
    FirstOrder.Derives.iffElimRight
      hIntersectionIff hDefinition
  have hBridge :
      ⊢ₘ[binary_intersection_operator_theory]
        pair_spec left right pair ⟶ₘ (intersection_spec pair binary ⟶ₘ
            binary_intersection_spec
              left right binary) :=
    FirstOrder.Derives.of_empty (pair_intersection_spec_implies_binary_intersection_spec
        left right pair binary
        hLeft hRight hPair hBinary)
  simpa [binary] using
    FirstOrder.Derives.impElim (FirstOrder.Derives.impElim
        hBridge hPairSpec)
      hIntersectionSpec
/-- 同一对集合的两个二元交候选必相等。 -/
theorem binary_intersection_unique (left right first second : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hFirst : Term.Admissible first SetSort.set) (hSecond : Term.Admissible second SetSort.set) :
    ⊢ₘ[extensionality_theory]
      binary_intersection_spec left right first ⟶ₘ (binary_intersection_spec left right second ⟶ₘ (first ≐ₘ second)) := by
  simpa [binary_intersection_spec,
    membership_specification] using
    membership_specification_unique
      first second ((bₛ#0 ∈ₘ left) ∧ₘ (bₛ#0 ∈ₘ right))
      hFirst hSecond (binary_intersection_spec_admissible
        hLeft hRight hFirst) (binary_intersection_spec_admissible
        hLeft hRight hSecond)
/-- 任意候选等于规范二元交项，当且仅当它满足成员合取规格。 -/
theorem binary_intersection_eq_iff_spec (left right candidate : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[binary_intersection_operator_theory] (candidate ≐ₘ (left ∩ₘ right)) ↔ₘ
        binary_intersection_spec
          left right candidate := by
  let binary :=
    binary_intersection_term left right
  let parameter :=
    FreshVariable.fresh_id SetSort.set
      [left ≐ₘ left, right ≐ₘ right]
  have hBinary :
      Term.Admissible binary SetSort.set :=
    binary_intersection_term_admissible
      left right hLeft hRight
  have hParameterFreshLeft : (SetSort.set, parameter) ∉
        Term.freeSupport left := by
    dsimp [parameter]
    have hFresh :=
      FreshVariable.fresh_id_not_mem_m (sort := SetSort.set) (formulas :=
          [left ≐ₘ left, right ≐ₘ right]) (formula := left ≐ₘ left) (by simp)
    simpa [Formula.freeSupport] using hFresh
  have hParameterFreshRight : (SetSort.set, parameter) ∉
        Term.freeSupport right := by
    dsimp [parameter]
    have hFresh :=
      FreshVariable.fresh_id_not_mem_m (sort := SetSort.set) (formulas :=
          [left ≐ₘ left, right ≐ₘ right]) (formula := right ≐ₘ right) (by simp)
    simpa [Formula.freeSupport] using hFresh
  have hLeftFixedCandidate :
      Term.substituteFree SetSort.set
          parameter candidate left =
        left :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter candidate left
      hParameterFreshLeft
  have hLeftFixedBinary :
      Term.substituteFree SetSort.set
          parameter binary left =
        left :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter binary left
      hParameterFreshLeft
  have hRightFixedCandidate :
      Term.substituteFree SetSort.set
          parameter candidate right =
        right :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter candidate right
      hParameterFreshRight
  have hRightFixedBinary :
      Term.substituteFree SetSort.set
          parameter binary right =
        right :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter binary right
      hParameterFreshRight
  have hEqualityAdmissible :
      Formula.Admissible (candidate ≐ₘ binary) :=
    Formula.Admissible.equal
      hCandidate hBinary
  have hCandidateSpecAdmissible :
      Formula.Admissible (binary_intersection_spec
          left right candidate) :=
    binary_intersection_spec_admissible
      hLeft hRight hCandidate
  change
    ⊢ₘ[binary_intersection_operator_theory] (candidate ≐ₘ binary) ↔ₘ
        binary_intersection_spec
          left right candidate
  apply FirstOrder.Derives.iffIntro
  · have hEquality :
        [candidate ≐ₘ binary]
          ⊢ₘ[binary_intersection_operator_theory]
            candidate ≐ₘ binary :=
      .assumption (by simp)
    have hCongruence :=
      Metatheory.Derives.equality_iff_of_equality (T := binary_intersection_operator_theory) (Γ := [candidate ≐ₘ binary]) (sort := SetSort.set)
        (eigen := parameter) (left := candidate) (right := binary) (body :=
          binary_intersection_spec
            left right (x#parameter))
        hEquality
    have hCongruenceNormalized :
        [candidate ≐ₘ binary]
          ⊢ₘ[binary_intersection_operator_theory]
            binary_intersection_spec
                left right candidate ↔ₘ
              binary_intersection_spec
                left right binary := by
      simpa [binary_intersection_spec,
        Formula.substituteFree,
        Term.substituteFree,
        hLeftFixedCandidate,
        hLeftFixedBinary,
        hRightFixedCandidate,
        hRightFixedBinary,
        set_variable] using hCongruence
    have hBinarySpec :
        [candidate ≐ₘ binary]
          ⊢ₘ[binary_intersection_operator_theory]
            binary_intersection_spec
              left right binary :=
      FirstOrder.Derives.context_weaken_cons (by
          simpa [binary] using
            binary_intersection_term_spec_derives
              left right hLeft hRight)
    exact FirstOrder.Derives.iffElimLeft
      hCongruenceNormalized hBinarySpec
  · have hCandidateSpec :
        [binary_intersection_spec left right candidate]
          ⊢ₘ[binary_intersection_operator_theory]
            binary_intersection_spec
              left right candidate :=
      .assumption (by simp)
    have hBinarySpec :
        [binary_intersection_spec left right candidate]
          ⊢ₘ[binary_intersection_operator_theory]
            binary_intersection_spec
              left right binary :=
      FirstOrder.Derives.context_weaken_cons (by
          simpa [binary] using
            binary_intersection_term_spec_derives
              left right hLeft hRight)
    have hUnique :
        [binary_intersection_spec left right candidate]
          ⊢ₘ[binary_intersection_operator_theory]
            binary_intersection_spec
                left right candidate ⟶ₘ (binary_intersection_spec
                  left right binary ⟶ₘ (candidate ≐ₘ binary)) :=
      FirstOrder.Derives.context_weaken_cons <|
        FirstOrder.Derives.theory_weaken (fun _ hFormula =>
            extensionality_theory_subset_binary_intersection_operator_theory
              hFormula) (binary_intersection_unique
            left right candidate binary
            hLeft hRight hCandidate hBinary)
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.impElim
        hUnique hCandidateSpec)
      hBinarySpec
/-- 两个参数的已证明等式可组合为二元交项等式。 -/
theorem binary_intersection_term_congr_of_equalities
    {Γ : Context signature} (left_first right_first left_second right_second : SetTerm) (hLeftFirst : Term.Admissible left_first SetSort.set)
    (hRightFirst : Term.Admissible right_first SetSort.set) (hLeftSecond : Term.Admissible left_second SetSort.set)
    (hRightSecond : Term.Admissible right_second SetSort.set) (hFirstEquality :
      Γ ⊢ₘ[binary_intersection_operator_theory]
        left_first ≐ₘ right_first) (hSecondEquality :
      Γ ⊢ₘ[binary_intersection_operator_theory]
        left_second ≐ₘ right_second) :
    Γ ⊢ₘ[binary_intersection_operator_theory] (left_first ∩ₘ left_second) ≐ₘ (right_first ∩ₘ right_second) := by
  exact Metatheory.Derives.binary_term_constructor_congr_of_equalities
    binary_intersection_term
    binary_intersection_term_admissible
    (by intros; simp [Term.substituteFree])
    left_first right_first left_second right_second
    hLeftFirst hRightFirst hLeftSecond hRightSecond
    hFirstEquality hSecondEquality
/-- 两组自由变量等式推出对应二元交项相等。 -/
theorem binary_intersection_term_congr (left_first right_first left_second right_second : FreeVarId) :
    ⊢ₘ[binary_intersection_operator_theory] (x#left_first ≐ₘ x#right_first) ⟶ₘ ((x#left_second ≐ₘ x#right_second) ⟶ₘ ((x#left_first ∩ₘ x#left_second) ≐ₘ
            (x#right_first ∩ₘ x#right_second))) := by
  have hLeftFirstAdmissible :=
    set_variable_admissible left_first
  have hRightFirstAdmissible :=
    set_variable_admissible right_first
  have hLeftSecondAdmissible :=
    set_variable_admissible left_second
  have hRightSecondAdmissible :=
    set_variable_admissible right_second
  have hFirstEqualityAdmissible :
      Formula.Admissible (x#left_first ≐ₘ x#right_first) :=
    Formula.Admissible.equal
      hLeftFirstAdmissible
      hRightFirstAdmissible
  have hSecondEqualityAdmissible :
      Formula.Admissible (x#left_second ≐ₘ x#right_second) :=
    Formula.Admissible.equal
      hLeftSecondAdmissible
      hRightSecondAdmissible
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  exact binary_intersection_term_congr_of_equalities (Γ :=
      [x#left_second ≐ₘ x#right_second,
        x#left_first ≐ₘ x#right_first]) (x#left_first) (x#right_first) (x#left_second) (x#right_second)
    hLeftFirstAdmissible
    hRightFirstAdmissible
    hLeftSecondAdmissible
    hRightSecondAdmissible
    (.assumption (by simp))
    (.assumption (by simp))
/-- 每个非空集合族都有交集的全称闭包。 -/
theorem intersection_exists_forall (family : FreeVarId) :
    ⊢ₘ[intersection_base_theory]
      ∀ₘ[SetSort.set, family],
        set_nonempty_condition (x#family) ⟶ₘ
          intersection_exists (x#family) := by
  have hOpen :
      ⊢ₘ[intersection_base_theory]
        set_nonempty_condition (x#family) ⟶ₘ
          intersection_exists (x#family) :=
    intersection_exists_derives (x#family) (set_variable_admissible family)
  derive_close (family) using hOpen
/-- 一元交候选图刻画的双变量全称闭包。 -/
theorem intersection_eq_iff_spec_forall (family candidate : FreeVarId) :
    ⊢ₘ[intersection_operator_theory]
      ∀ₘ[SetSort.set, family],
        ∀ₘ[SetSort.set, candidate],
          set_nonempty_condition (x#family) ⟶ₘ ((x#candidate ≐ₘ ⋂ₘ x#family) ↔ₘ
              intersection_spec (x#family) (x#candidate)) := by
  have hOpen :
      ⊢ₘ[intersection_operator_theory]
        set_nonempty_condition (x#family) ⟶ₘ ((x#candidate ≐ₘ ⋂ₘ x#family) ↔ₘ
            intersection_spec (x#family) (x#candidate)) :=
    intersection_eq_iff_spec (x#family) (x#candidate) (set_variable_admissible family) (set_variable_admissible candidate)
  derive_close (family, candidate) using hOpen
/-- 一元交函数项等式合同的双变量全称闭包。 -/
theorem intersection_term_congr_forall (left right : FreeVarId) :
    ⊢ₘ[intersection_operator_theory]
      ∀ₘ[SetSort.set, left],
        ∀ₘ[SetSort.set, right], (x#left ≐ₘ x#right) ⟶ₘ ((⋂ₘ x#left) ≐ₘ (⋂ₘ x#right)) := by
  derive_close (left, right) using
    intersection_term_congr left right
/-- 文献二元交候选图刻画的三变量全称闭包。 -/
theorem binary_intersection_eq_iff_descriptor_forall (left right candidate : FreeVarId) :
    ⊢ₘ[binary_intersection_operator_theory]
      ∀ₘ[SetSort.set, left],
        ∀ₘ[SetSort.set, right],
          ∀ₘ[SetSort.set, candidate], (x#candidate ≐ₘ (x#left ∩ₘ x#right)) ↔ₘ
              binary_intersection_descriptor (x#left) (x#right) (x#candidate) := by
  have hOpen :
      ⊢ₘ[binary_intersection_operator_theory] (x#candidate ≐ₘ (x#left ∩ₘ x#right)) ↔ₘ
          binary_intersection_descriptor (x#left) (x#right) (x#candidate) :=
    binary_intersection_eq_iff_descriptor (x#left) (x#right) (x#candidate) (set_variable_admissible left) (set_variable_admissible right)
      (set_variable_admissible candidate)
  derive_close (left, right, candidate) using hOpen
/-- 二元交成员合取规格的三变量全称闭包。 -/
theorem binary_intersection_eq_iff_spec_forall (left right candidate : FreeVarId) :
    ⊢ₘ[binary_intersection_operator_theory]
      ∀ₘ[SetSort.set, left],
        ∀ₘ[SetSort.set, right],
          ∀ₘ[SetSort.set, candidate], (x#candidate ≐ₘ (x#left ∩ₘ x#right)) ↔ₘ
              binary_intersection_spec (x#left) (x#right) (x#candidate) := by
  have hOpen :
      ⊢ₘ[binary_intersection_operator_theory] (x#candidate ≐ₘ (x#left ∩ₘ x#right)) ↔ₘ
          binary_intersection_spec (x#left) (x#right) (x#candidate) :=
    binary_intersection_eq_iff_spec (x#left) (x#right) (x#candidate) (set_variable_admissible left) (set_variable_admissible right)
      (set_variable_admissible candidate)
  derive_close (left, right, candidate) using hOpen
/-- 二元交函数项等式合同的四变量全称闭包。 -/
theorem binary_intersection_term_congr_forall (left_first right_first left_second right_second : FreeVarId) :
    ⊢ₘ[binary_intersection_operator_theory]
      ∀ₘ[SetSort.set, left_first],
        ∀ₘ[SetSort.set, right_first],
          ∀ₘ[SetSort.set, left_second],
            ∀ₘ[SetSort.set, right_second], (x#left_first ≐ₘ x#right_first) ⟶ₘ ((x#left_second ≐ₘ x#right_second) ⟶ₘ ((x#left_first ∩ₘ x#left_second) ≐ₘ
                    (x#right_first ∩ₘ x#right_second))) := by
  derive_close (left_first, right_first, left_second, right_second) using
    binary_intersection_term_congr
      left_first right_first left_second right_second
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
