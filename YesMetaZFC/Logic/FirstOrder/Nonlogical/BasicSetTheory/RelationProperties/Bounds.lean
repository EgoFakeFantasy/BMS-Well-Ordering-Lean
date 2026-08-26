import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.RelationProperties.Cartesian
/-!
# 关系平方界与反转性质
本模块收束关系的平方界、反转不变性及其文献全称闭包接口。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-! ## 关系的平方界 -/
/-- 关系的任意成员属于其双重并集的平方。 -/
theorem is_relation_member_mem_double_union_square (relation member : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hMember : Term.Admissible member SetSort.set) :
    ⊢ₘ[relation_plane_theory]
      is_relation_formula relation ⟶ₘ (member ∈ₘ relation) ⟶ₘ (member ∈ₘ (double_union_term relation ×ₘ
              double_union_term relation)) := by
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  let predicate : SetFormula :=
    is_relation_formula relation
  let membership : SetFormula :=
    member ∈ₘ relation
  let Γ : Context signature :=
    [membership, predicate]
  let left_coordinate := (member)₀ₘ
  let right_coordinate := (member)₁ₘ
  let represented :=
    ⟨left_coordinate, right_coordinate⟩ₘ
  let square :=
    double_union_term relation ×ₘ
      double_union_term relation
  have hDouble :
      Term.Admissible (double_union_term relation)
        SetSort.set :=
    double_union_term_admissible
      relation hRelation
  have hLeftCoordinate :
      Term.Admissible left_coordinate SetSort.set :=
    left_projection_term_admissible
      member hMember
  have hRightCoordinate :
      Term.Admissible right_coordinate SetSort.set :=
    right_projection_term_admissible
      member hMember
  have hRepresented :
      Term.Admissible represented SetSort.set :=
    ordered_pair_term_admissible
      left_coordinate right_coordinate
      hLeftCoordinate hRightCoordinate
  have hSquare :
      Term.Admissible square SetSort.set :=
    cartesian_product_term_admissible (double_union_term relation) (double_union_term relation)
      hDouble hDouble
  have hPredicate :
      Γ ⊢ₘ[relation_plane_theory]
        is_relation_formula relation := by
    simpa [Γ, predicate] using (show
        Γ ⊢ₘ[relation_plane_theory]
          predicate from
        .assumption (by simp [Γ]))
  have hMembership :
      Γ ⊢ₘ[relation_plane_theory]
        member ∈ₘ relation := by
    simpa [Γ, membership] using (show
        Γ ⊢ₘ[relation_plane_theory]
          membership from
        .assumption (by simp [Γ]))
  have hOrdered :
      Γ ⊢ₘ[relation_plane_theory]
        is_ordered_pair_formula member :=
    FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons <|
          FirstOrder.Derives.context_weaken_cons <|
          FirstOrder.Derives.theory_weaken (fun _ hFormula =>
              relation_predicate_theory_subset_relation_plane_theory
                hFormula) (is_relation_member_is_ordered_pair
              relation member hRelation hMember))
        hPredicate)
      hMembership
  have hRepresentationImp :
      Γ ⊢ₘ[relation_plane_theory]
        is_ordered_pair_formula member ⟶ₘ (member ≐ₘ represented) :=
    FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.theory_weaken (fun _ hFormula =>
          right_projection_operator_theory_subset_relation_plane_theory
            hFormula) (by
          simpa [left_coordinate, right_coordinate,
            represented] using
            is_ordered_pair_eq_ordered_pair_projections
              member hMember)
  have hRepresentation :
      Γ ⊢ₘ[relation_plane_theory]
        member ≐ₘ represented :=
    FirstOrder.Derives.impElim
      hRepresentationImp hOrdered
  have hCoordinates :
      Γ ⊢ₘ[relation_plane_theory] ((left_coordinate ∈ₘ
            double_union_term relation) ∧ₘ (right_coordinate ∈ₘ
            double_union_term relation)) :=
    FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons <|
          FirstOrder.Derives.context_weaken_cons <|
          ordered_pair_coordinates_mem_double_union
            relation member
            left_coordinate right_coordinate
            hRelation hMember
            hLeftCoordinate hRightCoordinate)
        hMembership)
      hRepresentation
  have hRepresentedInSquare :
      Γ ⊢ₘ[relation_plane_theory]
        represented ∈ₘ square :=
    FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons <|
          FirstOrder.Derives.context_weaken_cons <|
          ordered_pair_mem_cartesian_product (double_union_term relation) (double_union_term relation)
            left_coordinate right_coordinate
            hDouble hDouble
            hLeftCoordinate hRightCoordinate) (FirstOrder.Derives.conjElimLeft
          hCoordinates)) (FirstOrder.Derives.conjElimRight
        hCoordinates)
  have hTransport :=
    membership_left_iff_of_equality
      member represented square
      hMember hRepresented hSquare
      hRepresentation
  exact FirstOrder.Derives.iffElimLeft
    hTransport hRepresentedInSquare
/-- 关系成员可重构为其两个规范投影组成的有序对。 -/
theorem is_relation_member_eq_ordered_pair_projections (relation member : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hMember : Term.Admissible member SetSort.set) :
    ⊢ₘ[relation_plane_theory]
      is_relation_formula relation ⟶ₘ (member ∈ₘ relation) ⟶ₘ (member ≐ₘ
            ⟨(member)₀ₘ, (member)₁ₘ⟩ₘ) := by
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  let predicate : SetFormula :=
    is_relation_formula relation
  let membership : SetFormula :=
    member ∈ₘ relation
  let Γ : Context signature :=
    [membership, predicate]
  have hPredicate :
      Γ ⊢ₘ[relation_plane_theory]
        is_relation_formula relation := by
    simpa [Γ, predicate] using (show
        Γ ⊢ₘ[relation_plane_theory]
          predicate from
        .assumption (by simp [Γ]))
  have hMembership :
      Γ ⊢ₘ[relation_plane_theory]
        member ∈ₘ relation := by
    simpa [Γ, membership] using (show
        Γ ⊢ₘ[relation_plane_theory]
          membership from
        .assumption (by simp [Γ]))
  have hOrdered :
      Γ ⊢ₘ[relation_plane_theory]
        is_ordered_pair_formula member :=
    FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons <|
          FirstOrder.Derives.context_weaken_cons <|
          FirstOrder.Derives.theory_weaken (fun _ hFormula =>
              relation_predicate_theory_subset_relation_plane_theory
                hFormula) (is_relation_member_is_ordered_pair
              relation member hRelation hMember))
        hPredicate)
      hMembership
  have hRepresentationImp :
      Γ ⊢ₘ[relation_plane_theory]
        is_ordered_pair_formula member ⟶ₘ (member ≐ₘ
            ⟨(member)₀ₘ, (member)₁ₘ⟩ₘ) :=
    FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.theory_weaken (fun _ hFormula =>
          right_projection_operator_theory_subset_relation_plane_theory
            hFormula) (is_ordered_pair_eq_ordered_pair_projections
          member hMember)
  exact FirstOrder.Derives.impElim
    hRepresentationImp hOrdered
/-- 文献定理 2.36(3)：任意关系包含于其双重并集的平方。 -/
theorem is_relation_subset_double_union_square (relation : SetTerm) (hRelation : Term.Admissible relation SetSort.set) :
    ⊢ₘ[relation_plane_theory]
      is_relation_formula relation ⟶ₘ (relation ⊆ₘ (double_union_term relation ×ₘ
            double_union_term relation)) := by
  let predicate : SetFormula :=
    is_relation_formula relation
  let square :=
    double_union_term relation ×ₘ
      double_union_term relation
  let subset_body : SetFormula := (bₛ#0 ∈ₘ relation) ⟶ₘ (bₛ#0 ∈ₘ square)
  let member :=
    FreshVariable.fresh_id SetSort.set
      [predicate, subset_body]
  have hMemberFreshPredicate : (SetSort.set, member) freshForₘ
        predicate := by
    dsimp [member]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hMemberFreshSubset : (SetSort.set, member) freshForₘ
        subset_body := by
    dsimp [member]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hDouble :
      Term.Admissible (double_union_term relation)
        SetSort.set :=
    double_union_term_admissible
      relation hRelation
  have hSquare :
      Term.Admissible square SetSort.set :=
    cartesian_product_term_admissible (double_union_term relation) (double_union_term relation)
      hDouble hDouble
  have hRelationOpen :
      Term.openAt SetSort.set 0 (x#member) relation =
        relation :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#member)
      relation hRelation.2
  have hSquareOpen :
      Term.openAt SetSort.set 0 (x#member) square =
        square :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#member)
      square hSquare.2
  nd_apply FirstOrder.Derives.impIntro
  have hDefinition :
      [predicate] ⊢ₘ[relation_plane_theory]
        subset_definition_instance relation square :=
    FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.theory_weaken (fun _ hFormula =>
          subset_theory_subset_relation_plane_theory
            hFormula) (subset_definition_instance_derives_of_admissible
          relation square hRelation hSquare)
  have hAt :
      [predicate] ⊢ₘ[relation_plane_theory] (x#member ∈ₘ relation) ⟶ₘ (x#member ∈ₘ square) :=
    FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons (is_relation_member_mem_double_union_square
          relation (x#member)
          hRelation (set_variable_admissible member))) (show
        [predicate] ⊢ₘ[relation_plane_theory]
          is_relation_formula relation from
        .assumption (by simp [predicate]))
  have hAtOpened :
      [predicate] ⊢ₘ[relation_plane_theory]
        Formula.openAt SetSort.set 0 (x#member) subset_body := by
    simpa [subset_body, Formula.openAt,
      Term.openAt, hRelationOpen,
      hSquareOpen] using hAt
  have hCondition :
      [predicate] ⊢ₘ[relation_plane_theory]
        subset_condition relation square := by
    have hGeneralized :=
      FirstOrder.Derives.forall_intro (T := relation_plane_theory) (Γ := [predicate]) (sort := SetSort.set) (eigen := member) (body :=
          Formula.openAt SetSort.set 0 (x#member) subset_body) (by
          intro formula hFormula
          have hSentence :=
            relation_plane_theory_sentence hFormula
          rw [hSentence.2]
          simp) (by
          intro formula hFormula
          rcases List.mem_singleton.mp hFormula with rfl
          exact hMemberFreshPredicate)
        hAtOpened
    simpa [subset_condition,
      Formula.closeFreeAt_openAt
        SetSort.set member 0 subset_body
        hMemberFreshSubset] using hGeneralized
  exact FirstOrder.Derives.iffElimLeft
    hDefinition hCondition
/-- 文献定理 2.34 的现代存在性公式。 -/
def relation_square_witnesses (relation : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    ∃ₘ[SetSort.set], (bₛ#1 ≐ₘ double_union_term relation) ∧ₘ ((bₛ#0 ≐ₘ (bₛ#1 ×ₘ bₛ#1)) ∧ₘ (relation ⊆ₘ bₛ#0))
/-- 关系平方见证式保持 proof-carrying 公式边界。 -/
theorem relation_square_witnesses_admissible
    {relation : SetTerm} (hRelation : Term.Admissible
      relation SetSort.set) :
    Formula.Admissible (relation_square_witnesses relation) := by
  prove_admissible
/-- 文献定理 2.34：关系由双重并集平方所界定，两个规范项提供存在见证。 -/
theorem is_relation_implies_relation_square_witnesses (relation : SetTerm) (hRelation : Term.Admissible relation SetSort.set) :
    ⊢ₘ[relation_plane_theory]
      is_relation_formula relation ⟶ₘ
        relation_square_witnesses relation := by
  have hWitnessesAdmissible :
      Formula.Admissible (relation_square_witnesses relation) :=
    relation_square_witnesses_admissible
      hRelation
  nd_apply FirstOrder.Derives.impIntro
  let predicate : SetFormula :=
    is_relation_formula relation
  let double := double_union_term relation
  let square := double ×ₘ double
  have hDouble :
      Term.Admissible double SetSort.set :=
    double_union_term_admissible
      relation hRelation
  have hSquare :
      Term.Admissible square SetSort.set :=
    cartesian_product_term_admissible
      double double hDouble hDouble
  have hSubset :
      [predicate] ⊢ₘ[relation_plane_theory]
        relation ⊆ₘ square :=
    FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons (is_relation_subset_double_union_square
          relation hRelation)) (show
        [predicate] ⊢ₘ[relation_plane_theory]
          is_relation_formula relation from
        .assumption (by simp [predicate]))
  unfold relation_square_witnesses
  nd_apply FirstOrder.Derives.exists_intro (term := double)
  have hSquareExistentialAdmissible :
      Formula.Admissible (Formula.openAt SetSort.set 0 double (∃ₘ[SetSort.set], (bₛ#1 ≐ₘ
                double_union_term relation) ∧ₘ ((bₛ#0 ≐ₘ (bₛ#1 ×ₘ bₛ#1)) ∧ₘ (relation ⊆ₘ bₛ#0)))) :=
    Formula.Admissible.exists_openAt (σ := signature) (body :=
        ∃ₘ[SetSort.set], (bₛ#1 ≐ₘ
              double_union_term relation) ∧ₘ ((bₛ#0 ≐ₘ (bₛ#1 ×ₘ bₛ#1)) ∧ₘ (relation ⊆ₘ bₛ#0))) (term := double)
      SetSort.set (by
        simpa [relation_square_witnesses] using
          hWitnessesAdmissible)
      hDouble
  nd_apply FirstOrder.Derives.exists_intro (term := square)
  have hRelationOpen :
      Term.openAt SetSort.set 1 double relation =
        relation :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 double relation hRelation.2
  have hRelationOpenZero :
      Term.openAt SetSort.set 0 square relation =
        relation :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 square relation hRelation.2
  have hDoubleOpen :
      Term.openAt SetSort.set 0 square double =
        double :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 square double hDouble.2
  have hDoubleOpenOne :
      Term.openAt SetSort.set 1 double double =
        double :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 double double hDouble.2
  simpa [Formula.openAt, Formula.next_depth,
    Term.openAt, predicate, double, square,
    hRelationOpen, hRelationOpenZero,
    hDoubleOpen,
    hDoubleOpenOne] using (FirstOrder.Derives.conjIntro
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) double) (FirstOrder.Derives.conjIntro
        (FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set) square)
        hSubset))
/-- 文献定理 2.36(4)：关系成员反转后仍落在同一双重并集平方中。 -/
theorem is_relation_member_reverse_mem_double_union_square (relation member : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hMember : Term.Admissible member SetSort.set) :
    ⊢ₘ[relation_plane_theory]
      is_relation_formula relation ⟶ₘ (member ∈ₘ relation) ⟶ₘ (member⁻¹ₘ ∈ₘ (double_union_term relation ×ₘ
              double_union_term relation)) := by
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  let predicate : SetFormula :=
    is_relation_formula relation
  let membership : SetFormula :=
    member ∈ₘ relation
  let Γ : Context signature :=
    [membership, predicate]
  let left_coordinate := (member)₀ₘ
  let right_coordinate := (member)₁ₘ
  let represented :=
    ⟨left_coordinate, right_coordinate⟩ₘ
  let swapped :=
    ⟨right_coordinate, left_coordinate⟩ₘ
  let square :=
    double_union_term relation ×ₘ
      double_union_term relation
  have hDouble :
      Term.Admissible (double_union_term relation)
        SetSort.set :=
    double_union_term_admissible
      relation hRelation
  have hLeftCoordinate :
      Term.Admissible left_coordinate SetSort.set :=
    left_projection_term_admissible
      member hMember
  have hRightCoordinate :
      Term.Admissible right_coordinate SetSort.set :=
    right_projection_term_admissible
      member hMember
  have hRepresented :
      Term.Admissible represented SetSort.set :=
    ordered_pair_term_admissible
      left_coordinate right_coordinate
      hLeftCoordinate hRightCoordinate
  have hSwapped :
      Term.Admissible swapped SetSort.set :=
    ordered_pair_term_admissible
      right_coordinate left_coordinate
      hRightCoordinate hLeftCoordinate
  have hReverse :
      Term.Admissible member⁻¹ₘ SetSort.set :=
    ordered_pair_reverse_term_admissible
      member hMember
  have hSquare :
      Term.Admissible square SetSort.set :=
    cartesian_product_term_admissible (double_union_term relation) (double_union_term relation)
      hDouble hDouble
  have hPredicate :
      Γ ⊢ₘ[relation_plane_theory]
        is_relation_formula relation := by
    simpa [Γ, predicate] using (show
        Γ ⊢ₘ[relation_plane_theory]
          predicate from
        .assumption (by simp [Γ]))
  have hMembership :
      Γ ⊢ₘ[relation_plane_theory]
        member ∈ₘ relation := by
    simpa [Γ, membership] using (show
        Γ ⊢ₘ[relation_plane_theory]
          membership from
        .assumption (by simp [Γ]))
  have hRepresentation :
      Γ ⊢ₘ[relation_plane_theory]
        member ≐ₘ represented := by
    simpa [represented, left_coordinate,
      right_coordinate] using (FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons <|
            FirstOrder.Derives.context_weaken_cons <|
            is_relation_member_eq_ordered_pair_projections
              relation member hRelation hMember)
          hPredicate)
        hMembership)
  have hMemberInSquare :
      Γ ⊢ₘ[relation_plane_theory]
        member ∈ₘ square := by
    simpa [square] using (FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons <|
            FirstOrder.Derives.context_weaken_cons <|
            is_relation_member_mem_double_union_square
              relation member hRelation hMember)
          hPredicate)
        hMembership)
  have hRepresentationTransport :=
    membership_left_iff_of_equality
      member represented square
      hMember hRepresented hSquare
      hRepresentation
  have hRepresentedInSquare :
      Γ ⊢ₘ[relation_plane_theory]
        represented ∈ₘ square :=
    FirstOrder.Derives.iffElimRight
      hRepresentationTransport hMemberInSquare
  have hCoordinates :
      Γ ⊢ₘ[relation_plane_theory] ((left_coordinate ∈ₘ
            double_union_term relation) ∧ₘ (right_coordinate ∈ₘ
            double_union_term relation)) :=
    FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken_cons <|
        FirstOrder.Derives.context_weaken_cons <| by
          simpa [represented, square] using
            ordered_pair_mem_cartesian_product_iff_coordinates (double_union_term relation) (double_union_term relation)
              left_coordinate right_coordinate
              hDouble hDouble
              hLeftCoordinate hRightCoordinate)
      hRepresentedInSquare
  have hSwappedInSquare :
      Γ ⊢ₘ[relation_plane_theory]
        swapped ∈ₘ square :=
    FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons <|
          FirstOrder.Derives.context_weaken_cons <| by
            simpa [swapped, square] using
              ordered_pair_mem_cartesian_product (double_union_term relation) (double_union_term relation)
                right_coordinate left_coordinate
                hDouble hDouble
                hRightCoordinate hLeftCoordinate) (FirstOrder.Derives.conjElimRight
          hCoordinates)) (FirstOrder.Derives.conjElimLeft
        hCoordinates)
  have hReverseEquality :
      Γ ⊢ₘ[relation_plane_theory]
        member⁻¹ₘ ≐ₘ swapped :=
    FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.context_weaken_cons <| by
        simpa [ordered_pair_reverse_spec,
          swapped, left_coordinate,
          right_coordinate] using (FirstOrder.Derives.theory_weaken (fun _ hFormula =>
              ordered_pair_reverse_operator_theory_subset_relation_plane_theory
                hFormula) (ordered_pair_reverse_term_spec_derives
              member hMember))
  have hReverseTransport :=
    membership_left_iff_of_equality
      member⁻¹ₘ swapped square
      hReverse hSwapped hSquare
      hReverseEquality
  exact FirstOrder.Derives.iffElimLeft
    hReverseTransport hSwappedInSquare
/-! ## 有序对反转的结构性质 -/
/-- 反转函数项始终是由原项两个投影交换后组成的规范有序对。 -/
theorem ordered_pair_reverse_is_ordered_pair (pair : SetTerm) (hPair : Term.Admissible pair SetSort.set) :
    ⊢ₘ[relation_plane_theory]
      is_ordered_pair_formula pair⁻¹ₘ := by
  let left_projection := (pair)₀ₘ
  let right_projection := (pair)₁ₘ
  let reverse := pair⁻¹ₘ
  let swapped :=
    ⟨right_projection, left_projection⟩ₘ
  have hLeftProjection :
      Term.Admissible left_projection SetSort.set :=
    left_projection_term_admissible pair hPair
  have hRightProjection :
      Term.Admissible right_projection SetSort.set :=
    right_projection_term_admissible pair hPair
  have hReverse :
      Term.Admissible reverse SetSort.set :=
    ordered_pair_reverse_term_admissible
      pair hPair
  have hReverseEquality :
      ⊢ₘ[relation_plane_theory]
        reverse ≐ₘ swapped := by
    simpa [reverse, swapped,
      left_projection, right_projection,
      ordered_pair_reverse_spec] using (FirstOrder.Derives.theory_weaken (fun _ hFormula =>
          ordered_pair_reverse_operator_theory_subset_relation_plane_theory
            hFormula) (ordered_pair_reverse_term_spec_derives
          pair hPair))
  have hDefinition :
      ⊢ₘ[relation_plane_theory]
        is_ordered_pair_definition_instance reverse :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        relation_function_theory_subset_relation_plane_theory
          hFormula) (is_ordered_pair_definition_instance_derives
        reverse hReverse)
  have hCondition :
      ⊢ₘ[relation_plane_theory]
        is_ordered_pair_condition reverse := by
    have hConditionAdmissible :
        Formula.Admissible (is_ordered_pair_condition reverse) :=
      is_ordered_pair_condition_admissible
        hReverse
    unfold is_ordered_pair_condition
    nd_apply FirstOrder.Derives.exists_intro
      (term := right_projection)
    have hLeftExistentialAdmissible :
        Formula.Admissible (Formula.openAt SetSort.set 0
            right_projection (∃ₘ[SetSort.set],
              reverse ≐ₘ
                ⟨bₛ#1, bₛ#0⟩ₘ)) :=
      Formula.Admissible.exists_openAt (σ := signature) (body :=
          ∃ₘ[SetSort.set],
            reverse ≐ₘ
              ⟨bₛ#1, bₛ#0⟩ₘ) (term := right_projection)
        SetSort.set (by
          simpa [is_ordered_pair_condition] using
            hConditionAdmissible)
        hRightProjection
    nd_apply FirstOrder.Derives.exists_intro
      (term := left_projection)
    have hReverseOpenOne :
        Term.openAt SetSort.set 1
            right_projection reverse =
          reverse :=
      Term.openAt_eq_self_of_boundClosed
        SetSort.set 1 right_projection
        reverse hReverse.2
    have hReverseOpenZero :
        Term.openAt SetSort.set 0
            left_projection reverse =
          reverse :=
      Term.openAt_eq_self_of_boundClosed
        SetSort.set 0 left_projection
        reverse hReverse.2
    have hRightOpenZero :
        Term.openAt SetSort.set 0
            left_projection right_projection =
          right_projection :=
      Term.openAt_eq_self_of_boundClosed
        SetSort.set 0 left_projection
        right_projection hRightProjection.2
    simpa [Formula.openAt, Formula.next_depth,
      Term.openAt, swapped,
      hReverseOpenOne, hReverseOpenZero,
      hRightOpenZero] using hReverseEquality
  exact FirstOrder.Derives.iffElimLeft
    hDefinition hCondition
/-- 有序对与其反转具有相同的一元并集。 -/
theorem is_ordered_pair_implies_union_reverse_eq_union (pair : SetTerm) (hPair : Term.Admissible pair SetSort.set) :
    ⊢ₘ[relation_plane_theory]
      is_ordered_pair_formula pair ⟶ₘ ((⋃ₘ pair) ≐ₘ (⋃ₘ pair⁻¹ₘ)) := by
  nd_apply FirstOrder.Derives.impIntro
  let predicate := is_ordered_pair_formula pair
  let left_projection := (pair)₀ₘ
  let right_projection := (pair)₁ₘ
  let represented :=
    ⟨left_projection, right_projection⟩ₘ
  let swapped :=
    ⟨right_projection, left_projection⟩ₘ
  let coordinate_pair :=
    {left_projection, right_projection}ₘ
  let swapped_coordinate_pair :=
    {right_projection, left_projection}ₘ
  let reverse := pair⁻¹ₘ
  have hLeftProjection :
      Term.Admissible left_projection SetSort.set :=
    left_projection_term_admissible pair hPair
  have hRightProjection :
      Term.Admissible right_projection SetSort.set :=
    right_projection_term_admissible pair hPair
  have hRepresented :
      Term.Admissible represented SetSort.set :=
    ordered_pair_term_admissible
      left_projection right_projection
      hLeftProjection hRightProjection
  have hSwapped :
      Term.Admissible swapped SetSort.set :=
    ordered_pair_term_admissible
      right_projection left_projection
      hRightProjection hLeftProjection
  have hCoordinatePair :
      Term.Admissible coordinate_pair SetSort.set :=
    unordered_pair_term_admissible
      left_projection right_projection
      hLeftProjection hRightProjection
  have hSwappedCoordinatePair :
      Term.Admissible swapped_coordinate_pair
        SetSort.set :=
    unordered_pair_term_admissible
      right_projection left_projection
      hRightProjection hLeftProjection
  have hReverse :
      Term.Admissible reverse SetSort.set :=
    ordered_pair_reverse_term_admissible
      pair hPair
  have hUnionRepresented :
      Term.Admissible (⋃ₘ represented) SetSort.set :=
    union_term_admissible represented hRepresented
  have hUnionPair :
      Term.Admissible (⋃ₘ pair) SetSort.set :=
    union_term_admissible pair hPair
  have hUnionSwapped :
      Term.Admissible (⋃ₘ swapped) SetSort.set :=
    union_term_admissible swapped hSwapped
  have hUnionReverse :
      Term.Admissible (⋃ₘ reverse) SetSort.set :=
    union_term_admissible reverse hReverse
  have hPredicate :
      [predicate] ⊢ₘ[relation_plane_theory]
        is_ordered_pair_formula pair := by
    simpa [predicate] using (show
        [predicate] ⊢ₘ[relation_plane_theory]
          predicate from
        .assumption (by simp))
  have hRepresentation :
      [predicate] ⊢ₘ[relation_plane_theory]
        pair ≐ₘ represented := by
    simpa [represented, left_projection,
      right_projection] using (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons <|
          FirstOrder.Derives.theory_weaken (fun _ hFormula =>
              right_projection_operator_theory_subset_relation_plane_theory
                hFormula) (is_ordered_pair_eq_ordered_pair_projections
              pair hPair))
        hPredicate)
  have hReverseEquality :
      [predicate] ⊢ₘ[relation_plane_theory]
        reverse ≐ₘ swapped := by
    simpa [reverse, swapped,
      left_projection, right_projection,
      ordered_pair_reverse_spec] using (FirstOrder.Derives.context_weaken_cons <|
        FirstOrder.Derives.theory_weaken (fun _ hFormula =>
            ordered_pair_reverse_operator_theory_subset_relation_plane_theory
              hFormula) (ordered_pair_reverse_term_spec_derives
            pair hPair))
  have hUnionRepresentation :
      [predicate] ⊢ₘ[relation_plane_theory] (⋃ₘ pair) ≐ₘ (⋃ₘ represented) :=
    union_term_congr_of_equality
      pair represented hPair hRepresented
      hRepresentation
  have hUnionReverseEquality :
      [predicate] ⊢ₘ[relation_plane_theory] (⋃ₘ reverse) ≐ₘ (⋃ₘ swapped) :=
    union_term_congr_of_equality
      reverse swapped hReverse hSwapped
      hReverseEquality
  have hRepresentedUnion :
      [predicate] ⊢ₘ[relation_plane_theory] (⋃ₘ represented) ≐ₘ coordinate_pair := by
    simpa [represented, coordinate_pair,
      left_projection, right_projection] using (FirstOrder.Derives.context_weaken_cons (union_ordered_pair_term_eq_unordered_pair
          left_projection right_projection
          hLeftProjection hRightProjection))
  have hSwappedUnion :
      [predicate] ⊢ₘ[relation_plane_theory] (⋃ₘ swapped) ≐ₘ
          swapped_coordinate_pair := by
    simpa [swapped, swapped_coordinate_pair,
      left_projection, right_projection] using (FirstOrder.Derives.context_weaken_cons (union_ordered_pair_term_eq_unordered_pair
          right_projection left_projection
          hRightProjection hLeftProjection))
  have hCoordinateComm :
      [predicate] ⊢ₘ[relation_plane_theory]
        coordinate_pair ≐ₘ
          swapped_coordinate_pair := by
    simpa [coordinate_pair,
      swapped_coordinate_pair,
      left_projection, right_projection] using (FirstOrder.Derives.context_weaken_cons (unordered_pair_term_comm
          left_projection right_projection
          hLeftProjection hRightProjection))
  have hSwappedCoordinateToUnion :
      [predicate] ⊢ₘ[relation_plane_theory]
        swapped_coordinate_pair ≐ₘ (⋃ₘ swapped) :=
    Metatheory.Derives.equality_symm
      hSwappedUnion
  have hSwappedUnionToReverse :
      [predicate] ⊢ₘ[relation_plane_theory] (⋃ₘ swapped) ≐ₘ (⋃ₘ reverse) :=
    Metatheory.Derives.equality_symm
      hUnionReverseEquality
  have hPairUnionToCoordinate :
      [predicate] ⊢ₘ[relation_plane_theory] (⋃ₘ pair) ≐ₘ coordinate_pair :=
    Metatheory.Derives.equality_trans
      hUnionRepresentation hRepresentedUnion
  have hPairUnionToSwappedCoordinate :
      [predicate] ⊢ₘ[relation_plane_theory] (⋃ₘ pair) ≐ₘ
          swapped_coordinate_pair :=
    Metatheory.Derives.equality_trans
      hPairUnionToCoordinate hCoordinateComm
  have hPairUnionToSwappedUnion :
      [predicate] ⊢ₘ[relation_plane_theory] (⋃ₘ pair) ≐ₘ (⋃ₘ swapped) :=
    Metatheory.Derives.equality_trans
      hPairUnionToSwappedCoordinate
      hSwappedCoordinateToUnion
  simpa [reverse] using
    Metatheory.Derives.equality_trans
      hPairUnionToSwappedUnion
      hSwappedUnionToReverse
/--
文献定理 2.36(1)：有序对反转后仍是有序对，且一元并集保持不变。
-/
theorem is_ordered_pair_reverse_and_union_invariant (pair : SetTerm) (hPair : Term.Admissible pair SetSort.set) :
    ⊢ₘ[relation_plane_theory]
      is_ordered_pair_formula pair ⟶ₘ (is_ordered_pair_formula pair⁻¹ₘ ∧ₘ ((⋃ₘ pair) ≐ₘ (⋃ₘ pair⁻¹ₘ))) := by
  nd_apply FirstOrder.Derives.impIntro
  let predicate := is_ordered_pair_formula pair
  exact FirstOrder.Derives.conjIntro (FirstOrder.Derives.context_weaken_cons (ordered_pair_reverse_is_ordered_pair
        pair hPair)) (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons (is_ordered_pair_implies_union_reverse_eq_union
          pair hPair)) (show
        [predicate] ⊢ₘ[relation_plane_theory]
          is_ordered_pair_formula pair from
        .assumption (by simp [predicate])))
/-! ## 有序对刻画 -/
/-- 文献定理 2.35：有序对谓词等价于存在两个坐标使其等于规范有序对。 -/
theorem is_ordered_pair_iff_exists_coordinates (pair : SetTerm) (hPair : Term.Admissible pair SetSort.set) :
    ⊢ₘ[relation_plane_theory]
      is_ordered_pair_formula pair ↔ₘ
        is_ordered_pair_condition pair :=
  FirstOrder.Derives.theory_weaken (fun _ hFormula =>
      relation_function_theory_subset_relation_plane_theory
        hFormula) (is_ordered_pair_definition_instance_derives
      pair hPair)
/-- 有序对存在坐标刻画的全称闭包。 -/
theorem is_ordered_pair_iff_exists_coordinates_forall (pair : FreeVarId) :
    ⊢ₘ[relation_plane_theory]
      ∀ₘ[SetSort.set, pair],
        is_ordered_pair_formula (x#pair) ↔ₘ
          is_ordered_pair_condition (x#pair) := by
  derive_close (pair) using
    is_ordered_pair_iff_exists_coordinates (x#pair) (set_variable_admissible pair)
/-! ## 文献定理的全称闭包 -/
/-- 文献引理 2.7(1) 的双变量全称闭包。 -/
theorem member_subset_union_forall (source member : FreeVarId) :
    ⊢ₘ[relation_plane_theory]
      ∀ₘ[SetSort.set, source],
        ∀ₘ[SetSort.set, member], (x#member ∈ₘ x#source) ⟶ₘ (x#member ⊆ₘ ⋃ₘ x#source) := by
  derive_close (source, member) using
    member_subset_union (x#source) (x#member) (set_variable_admissible source) (set_variable_admissible member)
/-- 文献引理 2.7(2) 的双变量全称闭包。 -/
theorem union_mono_forall (left right : FreeVarId) :
    ⊢ₘ[relation_plane_theory]
      ∀ₘ[SetSort.set, left],
        ∀ₘ[SetSort.set, right], (x#left ⊆ₘ x#right) ⟶ₘ ((⋃ₘ x#left) ⊆ₘ (⋃ₘ x#right)) := by
  derive_close (left, right) using
    union_mono (x#left) (x#right) (set_variable_admissible left) (set_variable_admissible right)
/-- 文献定理 2.34 的单变量全称闭包。 -/
theorem is_relation_implies_relation_square_witnesses_forall (relation : FreeVarId) :
    ⊢ₘ[relation_plane_theory]
      ∀ₘ[SetSort.set, relation],
        is_relation_formula (x#relation) ⟶ₘ
          relation_square_witnesses (x#relation) := by
  derive_close (relation) using
    is_relation_implies_relation_square_witnesses (x#relation) (set_variable_admissible relation)
/-- 文献定理 2.36(1) 的单变量全称闭包。 -/
theorem is_ordered_pair_reverse_and_union_invariant_forall (pair : FreeVarId) :
    ⊢ₘ[relation_plane_theory]
      ∀ₘ[SetSort.set, pair],
        is_ordered_pair_formula (x#pair) ⟶ₘ (is_ordered_pair_formula (x#pair)⁻¹ₘ ∧ₘ ((⋃ₘ x#pair) ≐ₘ (⋃ₘ (x#pair)⁻¹ₘ))) := by
  derive_close (pair) using
    is_ordered_pair_reverse_and_union_invariant (x#pair) (set_variable_admissible pair)
/-- 文献定理 2.36(2) 的三变量全称闭包。 -/
theorem ordered_pair_mem_square_iff_swap_forall (source first second : FreeVarId) :
    ⊢ₘ[relation_plane_theory]
      ∀ₘ[SetSort.set, source],
        ∀ₘ[SetSort.set, first],
          ∀ₘ[SetSort.set, second], (⟨x#first, x#second⟩ₘ ∈ₘ (x#source ×ₘ x#source)) ↔ₘ (⟨x#second, x#first⟩ₘ ∈ₘ (x#source ×ₘ x#source)) := by
  derive_close (source, first, second) using
    ordered_pair_mem_square_iff_swap (x#source) (x#first) (x#second) (set_variable_admissible source) (set_variable_admissible first)
      (set_variable_admissible second)
/-- 文献定理 2.36(3) 的单变量全称闭包。 -/
theorem is_relation_subset_double_union_square_forall (relation : FreeVarId) :
    ⊢ₘ[relation_plane_theory]
      ∀ₘ[SetSort.set, relation],
        is_relation_formula (x#relation) ⟶ₘ (x#relation ⊆ₘ (double_union_term (x#relation) ×ₘ
              double_union_term (x#relation))) := by
  derive_close (relation) using
    is_relation_subset_double_union_square (x#relation) (set_variable_admissible relation)
/-- 文献定理 2.36(4) 的双变量全称闭包。 -/
theorem is_relation_member_reverse_mem_double_union_square_forall (relation member : FreeVarId) :
    ⊢ₘ[relation_plane_theory]
      ∀ₘ[SetSort.set, relation],
        ∀ₘ[SetSort.set, member],
          is_relation_formula (x#relation) ⟶ₘ (x#member ∈ₘ x#relation) ⟶ₘ ((x#member)⁻¹ₘ ∈ₘ (double_union_term (x#relation) ×ₘ
                  double_union_term (x#relation))) := by
  derive_close (relation, member) using
    is_relation_member_reverse_mem_double_union_square (x#relation) (x#member) (set_variable_admissible relation) (set_variable_admissible member)
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
