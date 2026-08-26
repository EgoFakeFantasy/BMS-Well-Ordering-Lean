import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.RelationProperties.Core
/-!
# 关系平面的笛卡尔积与坐标性质
本模块建立标准母集、坐标抽取与关系成员的双重并集坐标界。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-- 左侧成员生成的单点集包含于二元并。 -/
theorem singleton_subset_binary_union_left (left right element : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hElement : Term.Admissible element SetSort.set) :
    ⊢ₘ[relation_plane_theory] (element ∈ₘ left) ⟶ₘ ({element}ₘ ⊆ₘ (left ∪ₘ right)) := by
  have hInject :=
    mem_binary_union_left
      left right element
      hLeft hRight hElement
  have hSingleton :=
    singleton_subset_of_mem
      element (left ∪ₘ right)
      hElement (binary_union_term_admissible
        left right hLeft hRight)
  derive_prop
/-- 两侧成员生成的无序对包含于二元并。 -/
theorem unordered_pair_subset_binary_union (left right first second : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hFirst : Term.Admissible first SetSort.set) (hSecond : Term.Admissible second SetSort.set) :
    ⊢ₘ[relation_plane_theory] (first ∈ₘ left) ⟶ₘ (second ∈ₘ right) ⟶ₘ ({first, second}ₘ ⊆ₘ (left ∪ₘ right)) := by
  have hFirstInject :=
    mem_binary_union_left
      left right first
      hLeft hRight hFirst
  have hSecondInject :=
    mem_binary_union_right
      left right second
      hLeft hRight hSecond
  have hPairSubset :=
    unordered_pair_subset_of_members
      first second (left ∪ₘ right)
      hFirst hSecond (binary_union_term_admissible
        left right hLeft hRight)
  derive_prop
/-- 左侧成员生成的单点集属于二元并的幂集。 -/
theorem singleton_mem_power_set_binary_union (left right element : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hElement : Term.Admissible element SetSort.set) :
    ⊢ₘ[relation_plane_theory] (element ∈ₘ left) ⟶ₘ ({element}ₘ ∈ₘ
          power_set_binary_union_term
            left right) := by
  have hMembership :
      ⊢ₘ[relation_plane_theory] ({element}ₘ ∈ₘ
            power_set_binary_union_term
              left right) ↔ₘ ({element}ₘ ⊆ₘ (left ∪ₘ right)) :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        cartesian_product_operator_theory_subset_relation_plane_theory (cartesian_product_base_theory_subset_cartesian_product_operator_theory
            hFormula)) (mem_power_set_binary_union_term_iff_subset
        left right {element}ₘ
        hLeft hRight (singleton_term_admissible
          element hElement))
  have hSubset :=
    singleton_subset_binary_union_left
      left right element
      hLeft hRight hElement
  derive_prop
/-- 两侧成员生成的无序对属于二元并的幂集。 -/
theorem unordered_pair_mem_power_set_binary_union (left right first second : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hFirst : Term.Admissible first SetSort.set) (hSecond : Term.Admissible second SetSort.set) :
    ⊢ₘ[relation_plane_theory] (first ∈ₘ left) ⟶ₘ (second ∈ₘ right) ⟶ₘ ({first, second}ₘ ∈ₘ
            power_set_binary_union_term
              left right) := by
  have hMembership :
      ⊢ₘ[relation_plane_theory] ({first, second}ₘ ∈ₘ
            power_set_binary_union_term
              left right) ↔ₘ ({first, second}ₘ ⊆ₘ (left ∪ₘ right)) :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        cartesian_product_operator_theory_subset_relation_plane_theory (cartesian_product_base_theory_subset_cartesian_product_operator_theory
            hFormula)) (mem_power_set_binary_union_term_iff_subset
        left right {first, second}ₘ
        hLeft hRight (unordered_pair_term_admissible
          first second hFirst hSecond))
  have hSubset :=
    unordered_pair_subset_binary_union
      left right first second
      hLeft hRight hFirst hSecond
  derive_prop
/-- 坐标分别属于两侧集合时，Kuratowski 有序对包含于笛卡尔积的内层幂集。 -/
theorem ordered_pair_subset_power_set_binary_union (left right first second : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hFirst : Term.Admissible first SetSort.set) (hSecond : Term.Admissible second SetSort.set) :
    ⊢ₘ[relation_plane_theory] (first ∈ₘ left) ⟶ₘ (second ∈ₘ right) ⟶ₘ (⟨first, second⟩ₘ ⊆ₘ
            power_set_binary_union_term
              left right) := by
  let singleton := {first}ₘ
  let pair := {first, second}ₘ
  let ordered := ⟨first, second⟩ₘ
  let power :=
    power_set_binary_union_term left right
  have hSingleton :
      Term.Admissible singleton SetSort.set :=
    singleton_term_admissible first hFirst
  have hPair :
      Term.Admissible pair SetSort.set :=
    unordered_pair_term_admissible
      first second hFirst hSecond
  have hOrdered :
      Term.Admissible ordered SetSort.set :=
    ordered_pair_term_admissible
      first second hFirst hSecond
  have hPower :
      Term.Admissible power SetSort.set :=
    power_set_binary_union_term_admissible
      left right hLeft hRight
  have hSpec :
      ⊢ₘ[relation_plane_theory]
        pair_spec singleton pair ordered :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        ordered_pair_operator_theory_subset_relation_plane_theory
          hFormula) (by
        simpa [singleton, pair, ordered,
          ordered_pair_spec] using
          ordered_pair_term_spec_derives
            first second hFirst hSecond)
  have hSingletonMembership :
      ⊢ₘ[relation_plane_theory] (first ∈ₘ left) ⟶ₘ (singleton ∈ₘ power) := by
    simpa [singleton, power] using
      singleton_mem_power_set_binary_union
        left right first
        hLeft hRight hFirst
  have hPairMembership :
      ⊢ₘ[relation_plane_theory] (first ∈ₘ left) ⟶ₘ (second ∈ₘ right) ⟶ₘ (pair ∈ₘ power) := by
    simpa [pair, power] using
      unordered_pair_mem_power_set_binary_union
        left right first second
        hLeft hRight hFirst hSecond
  have hSubset :=
    pair_spec_implies_subset_of_members
      singleton pair ordered power
      hSingleton hPair hOrdered hPower
  derive_prop
/-- 坐标分别属于两侧集合时，规范有序对属于笛卡尔积的标准母集。 -/
theorem ordered_pair_mem_cartesian_product_bound (left right first second : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hFirst : Term.Admissible first SetSort.set) (hSecond : Term.Admissible second SetSort.set) :
    ⊢ₘ[relation_plane_theory] (first ∈ₘ left) ⟶ₘ (second ∈ₘ right) ⟶ₘ (⟨first, second⟩ₘ ∈ₘ
            cartesian_product_bound_term
              left right) := by
  have hMembership :
      ⊢ₘ[relation_plane_theory] (⟨first, second⟩ₘ ∈ₘ
            cartesian_product_bound_term
              left right) ↔ₘ (⟨first, second⟩ₘ ⊆ₘ
            power_set_binary_union_term
              left right) :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        cartesian_product_operator_theory_subset_relation_plane_theory (cartesian_product_base_theory_subset_cartesian_product_operator_theory
            hFormula)) (mem_cartesian_product_bound_term_iff_subset
        left right ⟨first, second⟩ₘ
        hLeft hRight (ordered_pair_term_admissible
          first second hFirst hSecond))
  have hSubset :=
    ordered_pair_subset_power_set_binary_union
      left right first second
      hLeft hRight hFirst hSecond
  derive_prop
/-- 坐标成员事实直接生成笛卡尔积的坐标成员条件。 -/
theorem ordered_pair_cartesian_product_member_condition (left right first second : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hFirst : Term.Admissible first SetSort.set) (hSecond : Term.Admissible second SetSort.set) :
    ⊢ₘ (first ∈ₘ left) ⟶ₘ (second ∈ₘ right) ⟶ₘ
          cartesian_product_member_condition
            left right ⟨first, second⟩ₘ := by
  have hOrderedPair :
      Term.Admissible (⟨first, second⟩ₘ) SetSort.set :=
    ordered_pair_term_admissible
      first second hFirst hSecond
  have hConditionAdmissible :
      Formula.Admissible (cartesian_product_member_condition
          left right ⟨first, second⟩ₘ) :=
    cartesian_product_member_condition_admissible
      hLeft hRight hOrderedPair
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  unfold cartesian_product_member_condition
  nd_apply FirstOrder.Derives.exists_intro (term := first)
  have hRightExistentialAdmissible :
      Formula.Admissible (Formula.openAt SetSort.set 0 first (∃ₘ[SetSort.set],
            bₛ#1 ∈ₘ left ∧ₘ (bₛ#0 ∈ₘ right ∧ₘ
                ⟨first, second⟩ₘ ≐ₘ
                  ⟨bₛ#1, bₛ#0⟩ₘ))) :=
    Formula.Admissible.exists_openAt (σ := signature) (body :=
        ∃ₘ[SetSort.set],
          bₛ#1 ∈ₘ left ∧ₘ (bₛ#0 ∈ₘ right ∧ₘ
              ⟨first, second⟩ₘ ≐ₘ
                ⟨bₛ#1, bₛ#0⟩ₘ)) (term := first)
      SetSort.set (by
        simpa [cartesian_product_member_condition] using
          hConditionAdmissible)
      hFirst
  nd_apply FirstOrder.Derives.exists_intro (term := second)
  have hLeftOpenOne :
      Term.openAt SetSort.set 1 first left =
        left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 first left hLeft.2
  have hLeftOpenZero :
      Term.openAt SetSort.set 0 second left =
        left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 second left hLeft.2
  have hFirstOpenOne :
      Term.openAt SetSort.set 1 first first =
        first :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 first first hFirst.2
  have hFirstOpenZero :
      Term.openAt SetSort.set 0 second first =
        first :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 second first hFirst.2
  have hRightOpenOne :
      Term.openAt SetSort.set 1 first right =
        right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 first right hRight.2
  have hRightOpenZero :
      Term.openAt SetSort.set 0 second right =
        right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 second right hRight.2
  have hSecondOpenOne :
      Term.openAt SetSort.set 1 first second =
        second :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 first second hSecond.2
  have hSecondOpenZero :
      Term.openAt SetSort.set 0 second second =
        second :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 second second hSecond.2
  simpa [Formula.openAt, Formula.next_depth,
    Term.openAt, hLeftOpenOne, hLeftOpenZero,
    hFirstOpenOne, hFirstOpenZero,
    hRightOpenOne, hRightOpenZero,
    hSecondOpenOne, hSecondOpenZero] using (FirstOrder.Derives.conjIntro (show
        [second ∈ₘ right, first ∈ₘ left] ⊢ₘ
          first ∈ₘ left from
        .assumption (by simp)) (FirstOrder.Derives.conjIntro (show
          [second ∈ₘ right, first ∈ₘ left] ⊢ₘ
            second ∈ₘ right from
          .assumption (by simp)) (FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set) ⟨first, second⟩ₘ)))
/-- 规范有序对属于笛卡尔积的正向坐标合同。 -/
theorem ordered_pair_mem_cartesian_product (left right first second : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hFirst : Term.Admissible first SetSort.set) (hSecond : Term.Admissible second SetSort.set) :
    ⊢ₘ[relation_plane_theory] (first ∈ₘ left) ⟶ₘ (second ∈ₘ right) ⟶ₘ (⟨first, second⟩ₘ ∈ₘ (left ×ₘ right)) := by
  have hSpec :
      ⊢ₘ[relation_plane_theory]
        cartesian_product_spec
          left right (left ×ₘ right) :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        cartesian_product_operator_theory_subset_relation_plane_theory
          hFormula) (cartesian_product_term_spec_derives
        left right hLeft hRight)
  have hPointImp :
      ⊢ₘ[relation_plane_theory]
        cartesian_product_spec
            left right (left ×ₘ right) ⟶ₘ ((⟨first, second⟩ₘ ∈ₘ (left ×ₘ right)) ↔ₘ ((⟨first, second⟩ₘ ∈ₘ
                cartesian_product_bound_term
                  left right) ∧ₘ
              cartesian_product_member_condition
                left right
                ⟨first, second⟩ₘ)) :=
    cartesian_product_spec_member_iff (T := relation_plane_theory) (Γ := [])
      left right (left ×ₘ right)
      ⟨first, second⟩ₘ
      hLeft hRight (cartesian_product_term_admissible
        left right hLeft hRight) (ordered_pair_term_admissible
        first second hFirst hSecond)
  have hPoint :
      ⊢ₘ[relation_plane_theory] (⟨first, second⟩ₘ ∈ₘ (left ×ₘ right)) ↔ₘ ((⟨first, second⟩ₘ ∈ₘ
              cartesian_product_bound_term
                left right) ∧ₘ
            cartesian_product_member_condition
              left right
              ⟨first, second⟩ₘ) :=
    FirstOrder.Derives.impElim
      hPointImp hSpec
  have hBound :=
    ordered_pair_mem_cartesian_product_bound
      left right first second
      hLeft hRight hFirst hSecond
  have hCondition :
      ⊢ₘ[relation_plane_theory] (first ∈ₘ left) ⟶ₘ (second ∈ₘ right) ⟶ₘ
            cartesian_product_member_condition
              left right ⟨first, second⟩ₘ :=
    FirstOrder.Derives.theory_weaken (by simp [Theory.empty]) (ordered_pair_cartesian_product_member_condition
        left right first second
        hLeft hRight hFirst hSecond)
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature :=
    [second ∈ₘ right, first ∈ₘ left]
  have hFirstMembership :
      Γ ⊢ₘ[relation_plane_theory]
        first ∈ₘ left :=
    .assumption (by simp [Γ])
  have hSecondMembership :
      Γ ⊢ₘ[relation_plane_theory]
        second ∈ₘ right :=
    .assumption (by simp [Γ])
  have hBoundInContext :
      Γ ⊢ₘ[relation_plane_theory]
        ⟨first, second⟩ₘ ∈ₘ
          cartesian_product_bound_term
            left right :=
    FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons <|
          FirstOrder.Derives.context_weaken_cons
            hBound)
        hFirstMembership)
      hSecondMembership
  have hConditionInContext :
      Γ ⊢ₘ[relation_plane_theory]
        cartesian_product_member_condition
          left right ⟨first, second⟩ₘ :=
    FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons <|
          FirstOrder.Derives.context_weaken_cons
            hCondition)
        hFirstMembership)
      hSecondMembership
  exact FirstOrder.Derives.iffElimLeft (FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.context_weaken_cons hPoint) (FirstOrder.Derives.conjIntro
      hBoundInContext hConditionInContext)
/-! ## 笛卡尔积的坐标抽取 -/
/-- 规范有序对满足笛卡尔积成员条件时，其两个坐标分别属于左右集合。 -/
theorem ordered_pair_member_condition_implies_coordinates (left right first second : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hFirst : Term.Admissible first SetSort.set) (hSecond : Term.Admissible second SetSort.set) :
    ⊢ₘ[relation_plane_theory]
      cartesian_product_member_condition
          left right ⟨first, second⟩ₘ ⟶ₘ ((first ∈ₘ left) ∧ₘ (second ∈ₘ right)) := by
  let condition :=
    cartesian_product_member_condition
      left right ⟨first, second⟩ₘ
  let conclusion : SetFormula := (first ∈ₘ left) ∧ₘ (second ∈ₘ right)
  let outer_body : SetFormula :=
    ∃ₘ[SetSort.set], (bₛ#1 ∈ₘ left) ∧ₘ ((bₛ#0 ∈ₘ right) ∧ₘ (⟨first, second⟩ₘ ≐ₘ
            ⟨bₛ#1, bₛ#0⟩ₘ))
  let left_witness :=
    FreshVariable.fresh_id SetSort.set
      [condition, conclusion, outer_body]
  let outer_point :=
    Formula.openAt SetSort.set 0 (x#left_witness) outer_body
  let inner_body : SetFormula := (x#left_witness ∈ₘ left) ∧ₘ ((bₛ#0 ∈ₘ right) ∧ₘ (⟨first, second⟩ₘ ≐ₘ
          ⟨x#left_witness, bₛ#0⟩ₘ))
  let right_witness :=
    FreshVariable.fresh_id SetSort.set
      [condition, conclusion, outer_body,
        outer_point, inner_body]
  let inner_point :=
    Formula.openAt SetSort.set 0 (x#right_witness) inner_body
  have hLeftWitnessFreshCondition : (SetSort.set, left_witness) freshForₘ
        condition := by
    dsimp [left_witness]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hLeftWitnessFreshConclusion : (SetSort.set, left_witness) freshForₘ
        conclusion := by
    dsimp [left_witness]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hLeftWitnessFreshOuterBody : (SetSort.set, left_witness) freshForₘ
        outer_body := by
    dsimp [left_witness]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hRightWitnessFreshCondition : (SetSort.set, right_witness) freshForₘ
        condition := by
    dsimp [right_witness]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hRightWitnessFreshOuterPoint : (SetSort.set, right_witness) freshForₘ
        outer_point := by
    dsimp [right_witness]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hRightWitnessFreshConclusion : (SetSort.set, right_witness) freshForₘ
        conclusion := by
    dsimp [right_witness]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hRightWitnessFreshInnerBody : (SetSort.set, right_witness) freshForₘ
        inner_body := by
    dsimp [right_witness]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hConditionAdmissible :
      Formula.Admissible condition := by
    dsimp [condition]
    exact
      cartesian_product_member_condition_admissible
        hLeft hRight (ordered_pair_term_admissible
          first second hFirst hSecond)
  have hConclusionAdmissible :
      Formula.Admissible conclusion := by
    dsimp [conclusion]
    exact Formula.Admissible.conj (membership_formula_admissible
        hFirst hLeft) (membership_formula_admissible
        hSecond hRight)
  have hOuterPointAdmissible :
      Formula.Admissible outer_point := by
    simpa [condition, outer_point, outer_body,
      cartesian_product_member_condition] using (Formula.Admissible.exists_openAt (σ := signature) (body := outer_body) (term := x#left_witness)
        SetSort.set (by
          simpa [condition,
            cartesian_product_member_condition,
            outer_body] using
            hConditionAdmissible) (set_variable_admissible left_witness))
  nd_apply FirstOrder.Derives.impIntro
  have hCondition :
      [condition] ⊢ₘ[relation_plane_theory]
        condition :=
    .assumption (by simp)
  have hOuterExists :
      [condition] ⊢ₘ[relation_plane_theory]
        ∃ₘ[SetSort.set],
          Formula.closeFreeAt
            SetSort.set left_witness 0 outer_point := by
    have hCloseOpen :
        Formula.closeFreeAt
            SetSort.set left_witness 0 outer_point =
          outer_body := by
      dsimp [outer_point]
      exact Formula.closeFreeAt_openAt
        SetSort.set left_witness 0
        outer_body hLeftWitnessFreshOuterBody
    simpa [condition,
      cartesian_product_member_condition,
      outer_body, hCloseOpen] using hCondition
  have hOuterCase :
      outer_point :: [condition]
        ⊢ₘ[relation_plane_theory]
          conclusion := by
    have hOuterPointShape :
        outer_point = (∃ₘ[SetSort.set], inner_body) := by
      simp [outer_point, outer_body, inner_body,
        Formula.openAt, Formula.next_depth,
        Term.openAt,
        Term.openAt_eq_self_of_boundClosed
          SetSort.set 1 (x#left_witness)
          left hLeft.2,
        Term.openAt_eq_self_of_boundClosed
          SetSort.set 1 (x#left_witness)
          right hRight.2,
        Term.openAt_eq_self_of_boundClosed
          SetSort.set 1 (x#left_witness)
          first hFirst.2,
        Term.openAt_eq_self_of_boundClosed
          SetSort.set 1 (x#left_witness)
          second hSecond.2]
    have hInnerExists :
        outer_point :: [condition]
          ⊢ₘ[relation_plane_theory]
            ∃ₘ[SetSort.set], inner_body := by
      rw [← hOuterPointShape]
      exact .assumption (by simp)
    have hInnerExistentialAdmissible :
        Formula.Admissible (∃ₘ[SetSort.set], inner_body) := by
      simpa [hOuterPointShape] using
        hOuterPointAdmissible
    have hInnerPointAdmissible :
        Formula.Admissible inner_point := by
      simpa [inner_point] using (Formula.Admissible.exists_openAt (σ := signature) (body := inner_body) (term := x#right_witness)
          SetSort.set
          hInnerExistentialAdmissible (set_variable_admissible
            right_witness))
    have hInnerExistsClosed :
        outer_point :: [condition]
          ⊢ₘ[relation_plane_theory]
            ∃ₘ[SetSort.set],
              Formula.closeFreeAt
                SetSort.set right_witness 0
                inner_point := by
      have hCloseOpen :
          Formula.closeFreeAt
              SetSort.set right_witness 0
              inner_point =
            inner_body := by
        dsimp [inner_point]
        exact Formula.closeFreeAt_openAt
          SetSort.set right_witness 0
          inner_body hRightWitnessFreshInnerBody
      simpa [hCloseOpen] using hInnerExists
    have hInnerCase :
        inner_point :: outer_point :: [condition]
          ⊢ₘ[relation_plane_theory]
            conclusion := by
      let Γ : Context signature :=
        inner_point :: outer_point :: [condition]
      have hInnerPointShape :
          inner_point = ((x#left_witness ∈ₘ left) ∧ₘ ((x#right_witness ∈ₘ right) ∧ₘ (⟨first, second⟩ₘ ≐ₘ
                  ⟨x#left_witness,
                    x#right_witness⟩ₘ))) := by
        simp [inner_point, inner_body,
          Formula.openAt, Term.openAt,
          Term.openAt_eq_self_of_boundClosed
            SetSort.set 0 (x#right_witness)
            left hLeft.2,
          Term.openAt_eq_self_of_boundClosed
            SetSort.set 0 (x#right_witness)
            right hRight.2,
          Term.openAt_eq_self_of_boundClosed
            SetSort.set 0 (x#right_witness)
            first hFirst.2,
          Term.openAt_eq_self_of_boundClosed
            SetSort.set 0 (x#right_witness)
            second hSecond.2]
      have hData :
          Γ ⊢ₘ[relation_plane_theory] ((x#left_witness ∈ₘ left) ∧ₘ ((x#right_witness ∈ₘ right) ∧ₘ (⟨first, second⟩ₘ ≐ₘ
                  ⟨x#left_witness,
                    x#right_witness⟩ₘ))) := by
        rw [← hInnerPointShape]
        exact .assumption (by simp [Γ])
      have hPairEquality :
          Γ ⊢ₘ[relation_plane_theory]
            ⟨first, second⟩ₘ ≐ₘ
              ⟨x#left_witness,
                x#right_witness⟩ₘ :=
        FirstOrder.Derives.conjElimRight (FirstOrder.Derives.conjElimRight
            hData)
      have hCoordinateIff :
          Γ ⊢ₘ[relation_plane_theory] (⟨first, second⟩ₘ ≐ₘ
                ⟨x#left_witness,
                  x#right_witness⟩ₘ) ↔ₘ ((first ≐ₘ x#left_witness) ∧ₘ (second ≐ₘ x#right_witness)) :=
        FirstOrder.Derives.context_weaken (by
            intro formula hFormula
            exact False.elim (List.not_mem_nil hFormula)) (FirstOrder.Derives.theory_weaken (fun _ hFormula =>
              ordered_pair_operator_theory_subset_relation_plane_theory
                hFormula) (ordered_pair_term_eq_iff_coordinates
              first second (x#left_witness) (x#right_witness)
              hFirst hSecond (set_variable_admissible left_witness) (set_variable_admissible right_witness)))
      have hCoordinateEqualities :
          Γ ⊢ₘ[relation_plane_theory] ((first ≐ₘ x#left_witness) ∧ₘ (second ≐ₘ x#right_witness)) :=
        FirstOrder.Derives.iffElimRight
          hCoordinateIff hPairEquality
      have hFirstTransport :=
        membership_left_iff_of_equality
          first (x#left_witness) left
          hFirst (set_variable_admissible left_witness)
          hLeft (FirstOrder.Derives.conjElimLeft
            hCoordinateEqualities)
      have hSecondTransport :=
        membership_left_iff_of_equality
          second (x#right_witness) right
          hSecond (set_variable_admissible right_witness)
          hRight (FirstOrder.Derives.conjElimRight
            hCoordinateEqualities)
      exact FirstOrder.Derives.conjIntro (FirstOrder.Derives.iffElimLeft
          hFirstTransport (FirstOrder.Derives.conjElimLeft hData)) (FirstOrder.Derives.iffElimLeft
          hSecondTransport (FirstOrder.Derives.conjElimLeft (FirstOrder.Derives.conjElimRight
              hData)))
    exact FirstOrder.Derives.exists_elim (by
        intro formula hFormula
        have hSentence :=
          relation_plane_theory_sentence hFormula
        rw [hSentence.2]
        simp) (by
        intro formula hFormula
        rcases List.mem_cons.mp hFormula with rfl | hFormula
        · exact hRightWitnessFreshOuterPoint
        · rcases List.mem_singleton.mp hFormula with rfl
          exact hRightWitnessFreshCondition)
      hRightWitnessFreshConclusion
      hInnerExistsClosed hInnerCase
  exact FirstOrder.Derives.exists_elim (by
      intro formula hFormula
      have hSentence :=
        relation_plane_theory_sentence hFormula
      rw [hSentence.2]
      simp) (by
      intro formula hFormula
      rcases List.mem_singleton.mp hFormula with rfl
      exact hLeftWitnessFreshCondition)
    hLeftWitnessFreshConclusion
    hOuterExists hOuterCase
/-- 规范有序对属于笛卡尔积，当且仅当两个坐标分别属于左右集合。 -/
theorem ordered_pair_mem_cartesian_product_iff_coordinates (left right first second : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hFirst : Term.Admissible first SetSort.set) (hSecond : Term.Admissible second SetSort.set) :
    ⊢ₘ[relation_plane_theory] (⟨first, second⟩ₘ ∈ₘ (left ×ₘ right)) ↔ₘ ((first ∈ₘ left) ∧ₘ (second ∈ₘ right)) := by
  have hSpec :
      ⊢ₘ[relation_plane_theory]
        cartesian_product_spec
          left right (left ×ₘ right) :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        cartesian_product_operator_theory_subset_relation_plane_theory
          hFormula) (cartesian_product_term_spec_derives
        left right hLeft hRight)
  have hPointImp :
      ⊢ₘ[relation_plane_theory]
        cartesian_product_spec
            left right (left ×ₘ right) ⟶ₘ ((⟨first, second⟩ₘ ∈ₘ (left ×ₘ right)) ↔ₘ ((⟨first, second⟩ₘ ∈ₘ
                cartesian_product_bound_term
                  left right) ∧ₘ
              cartesian_product_member_condition
                left right
                ⟨first, second⟩ₘ)) :=
    cartesian_product_spec_member_iff (T := relation_plane_theory) (Γ := [])
      left right (left ×ₘ right)
      ⟨first, second⟩ₘ
      hLeft hRight (cartesian_product_term_admissible
        left right hLeft hRight) (ordered_pair_term_admissible
        first second hFirst hSecond)
  have hPoint :=
    FirstOrder.Derives.impElim hPointImp hSpec
  have hConditionToCoordinates :=
    ordered_pair_member_condition_implies_coordinates
      left right first second
      hLeft hRight hFirst hSecond
  have hCoordinatesToMembership :=
    ordered_pair_mem_cartesian_product
      left right first second
      hLeft hRight hFirst hSecond
  apply FirstOrder.Derives.iffIntro
  ·
    have hData :=
      FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken_cons hPoint) (show
          [⟨first, second⟩ₘ ∈ₘ (left ×ₘ right)]
            ⊢ₘ[relation_plane_theory]
              ⟨first, second⟩ₘ ∈ₘ (left ×ₘ right) from
          .assumption (by simp))
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons
        hConditionToCoordinates) (FirstOrder.Derives.conjElimRight hData)
  ·
    let coordinates : SetFormula := (first ∈ₘ left) ∧ₘ (second ∈ₘ right)
    have hMembershipImp :
        [coordinates] ⊢ₘ[relation_plane_theory] (first ∈ₘ left) ⟶ₘ (second ∈ₘ right) ⟶ₘ (⟨first, second⟩ₘ ∈ₘ (left ×ₘ right)) :=
      FirstOrder.Derives.context_weaken_cons
        hCoordinatesToMembership
    have hCoordinates :
        [coordinates] ⊢ₘ[relation_plane_theory]
          coordinates :=
      .assumption (by simp)
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.impElim
        hMembershipImp (FirstOrder.Derives.conjElimLeft
          hCoordinates)) (FirstOrder.Derives.conjElimRight
        hCoordinates)
/-- 文献定理 2.36(2)：同一平方中的规范有序对对坐标交换封闭。 -/
theorem ordered_pair_mem_square_iff_swap (source first second : SetTerm) (hSource : Term.Admissible source SetSort.set)
    (hFirst : Term.Admissible first SetSort.set) (hSecond : Term.Admissible second SetSort.set) :
    ⊢ₘ[relation_plane_theory] (⟨first, second⟩ₘ ∈ₘ (source ×ₘ source)) ↔ₘ (⟨second, first⟩ₘ ∈ₘ (source ×ₘ source)) := by
  have hForward :=
    ordered_pair_mem_cartesian_product_iff_coordinates
      source source first second
      hSource hSource hFirst hSecond
  have hBackward :=
    ordered_pair_mem_cartesian_product_iff_coordinates
      source source second first
      hSource hSource hSecond hFirst
  derive_prop
/-! ## 关系成员的双重并集坐标界 -/
/-- 一个关系成员按规范有序对表示时，两个坐标都属于该关系的双重并集。 -/
theorem ordered_pair_coordinates_mem_double_union (relation member first second : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hMember : Term.Admissible member SetSort.set) (hFirst : Term.Admissible first SetSort.set) (hSecond : Term.Admissible second SetSort.set) :
    ⊢ₘ[relation_plane_theory] (member ∈ₘ relation) ⟶ₘ (member ≐ₘ ⟨first, second⟩ₘ) ⟶ₘ ((first ∈ₘ double_union_term relation) ∧ₘ
            (second ∈ₘ double_union_term relation)) := by
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  let membership : SetFormula :=
    member ∈ₘ relation
  let representation : SetFormula :=
    member ≐ₘ ⟨first, second⟩ₘ
  let Γ : Context signature :=
    [representation, membership]
  let singleton := {first}ₘ
  let pair := {first, second}ₘ
  let ordered := ⟨first, second⟩ₘ
  have hSingleton :
      Term.Admissible singleton SetSort.set :=
    singleton_term_admissible first hFirst
  have hPair :
      Term.Admissible pair SetSort.set :=
    unordered_pair_term_admissible
      first second hFirst hSecond
  have hOrdered :
      Term.Admissible ordered SetSort.set :=
    ordered_pair_term_admissible
      first second hFirst hSecond
  have hRepresentation :
      Γ ⊢ₘ[relation_plane_theory]
        member ≐ₘ ordered := by
    simpa [Γ, representation, ordered] using (show
        Γ ⊢ₘ[relation_plane_theory]
          representation from
        .assumption (by simp [Γ]))
  have hMembership :
      Γ ⊢ₘ[relation_plane_theory]
        member ∈ₘ relation := by
    simpa [Γ, membership] using (show
        Γ ⊢ₘ[relation_plane_theory]
          membership from
        .assumption (by simp [Γ]))
  have hSingletonInOrdered :
      Γ ⊢ₘ[relation_plane_theory]
        singleton ∈ₘ ordered :=
    FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.context_weaken_cons <| by
        simpa [singleton, ordered] using
          singleton_mem_ordered_pair
            first second hFirst hSecond
  have hPairInOrdered :
      Γ ⊢ₘ[relation_plane_theory]
        pair ∈ₘ ordered :=
    FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.context_weaken_cons <| by
        simpa [pair, ordered] using
          unordered_pair_mem_ordered_pair
            first second hFirst hSecond
  have hSingletonTransport :=
    membership_right_iff_of_equality
      singleton member ordered
      hSingleton hMember hOrdered
      hRepresentation
  have hPairTransport :=
    membership_right_iff_of_equality
      pair member ordered
      hPair hMember hOrdered
      hRepresentation
  have hSingletonInMember :
      Γ ⊢ₘ[relation_plane_theory]
        singleton ∈ₘ member :=
    FirstOrder.Derives.iffElimLeft
      hSingletonTransport hSingletonInOrdered
  have hPairInMember :
      Γ ⊢ₘ[relation_plane_theory]
        pair ∈ₘ member :=
    FirstOrder.Derives.iffElimLeft
      hPairTransport hPairInOrdered
  have hSingletonInUnion :
      Γ ⊢ₘ[relation_plane_theory]
        singleton ∈ₘ ⋃ₘ relation := by
    have hStep :=
      mem_union_of_mem_of_mem
        relation member singleton
        hRelation hMember hSingleton
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons <|
          FirstOrder.Derives.context_weaken_cons hStep)
        hMembership)
      hSingletonInMember
  have hPairInUnion :
      Γ ⊢ₘ[relation_plane_theory]
        pair ∈ₘ ⋃ₘ relation := by
    have hStep :=
      mem_union_of_mem_of_mem
        relation member pair
        hRelation hMember hPair
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons <|
          FirstOrder.Derives.context_weaken_cons hStep)
        hMembership)
      hPairInMember
  have hFirstInSingleton :
      Γ ⊢ₘ[relation_plane_theory]
        first ∈ₘ singleton :=
    FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.context_weaken_cons <| by
        simpa [singleton] using
          mem_singleton_self first hFirst
  have hSecondInPair :
      Γ ⊢ₘ[relation_plane_theory]
        second ∈ₘ pair :=
    FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.context_weaken_cons <| by
        simpa [pair] using
          mem_unordered_pair_right
            first second hFirst hSecond
  have hFirstInDouble :
      Γ ⊢ₘ[relation_plane_theory]
        first ∈ₘ double_union_term relation := by
    have hStep :=
      mem_union_of_mem_of_mem (⋃ₘ relation) singleton first (union_term_admissible relation hRelation)
        hSingleton hFirst
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons <|
          FirstOrder.Derives.context_weaken_cons hStep)
        hSingletonInUnion)
      hFirstInSingleton
  have hSecondInDouble :
      Γ ⊢ₘ[relation_plane_theory]
        second ∈ₘ double_union_term relation := by
    have hStep :=
      mem_union_of_mem_of_mem (⋃ₘ relation) pair second (union_term_admissible relation hRelation)
        hPair hSecond
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons <|
          FirstOrder.Derives.context_weaken_cons hStep)
        hPairInUnion)
      hSecondInPair
  exact FirstOrder.Derives.conjIntro
    hFirstInDouble hSecondInDouble
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
