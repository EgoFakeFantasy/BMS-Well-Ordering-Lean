import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.RelationProperties.Cartesian

/-!
# 关系平方界与反转性质

关系平方界由投影重构、双重并集坐标界和笛卡尔积坐标合同直接组合。文献中的
全称闭包不再作为按自然数编号变量的兼容接口保存；公共定理直接量化类型化 free
上下文。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-! ## 关系的平方界 -/

/-- 关系成员可重构为其两个规范投影组成的有序对。 -/
theorem is_relation_member_eq_ordered_pair_projections
    {free : SetContext} {Γ : Context signature free}
    (relation member : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      is_relation_formula relation ⟶ₘ
        ((member ∈ₘ relation) ⟶ₘ
          (member ≐ₘ ⟨(member)₀ₘ, (member)₁ₘ⟩ₘ)) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free :=
    (member ∈ₘ relation) :: is_relation_formula relation :: Γ
  have hOrdered := FirstOrder.Derives.imp_elim
    (FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.theory_weaken
        relation_predicate_theory_subset_relation_plane_theory
        (is_relation_member_is_ordered_pair
          (Γ := Δ) relation member))
      (FirstOrder.Derives.assumption (by simp [Δ])))
    (FirstOrder.Derives.assumption (by simp [Δ]))
  exact FirstOrder.Derives.imp_elim
    (FirstOrder.Derives.theory_weaken
      right_projection_operator_theory_subset_relation_plane_theory
      (is_ordered_pair_eq_ordered_pair_projections
        (Γ := Δ) member))
    hOrdered

/-- 关系的任意成员属于其双重并集的平方。 -/
theorem is_relation_member_mem_double_union_square
    {free : SetContext} {Γ : Context signature free}
    (relation member : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      is_relation_formula relation ⟶ₘ
        ((member ∈ₘ relation) ⟶ₘ
          (member ∈ₘ
            (double_union_term relation ×ₘ
              double_union_term relation))) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free :=
    (member ∈ₘ relation) :: is_relation_formula relation :: Γ
  let left : SetOpenTerm free := (member)₀ₘ
  let right : SetOpenTerm free := (member)₁ₘ
  let represented : SetOpenTerm free := ⟨left, right⟩ₘ
  let double : SetOpenTerm free := double_union_term relation
  let square : SetOpenTerm free := double ×ₘ double
  have hPredicate : Δ ⊢ₘ[relation_plane_theory]
      is_relation_formula relation :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hMembership : Δ ⊢ₘ[relation_plane_theory]
      member ∈ₘ relation :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hRepresentation : Δ ⊢ₘ[relation_plane_theory]
      member ≐ₘ represented := by
    simpa [left, right, represented] using
      FirstOrder.Derives.imp_elim
        (FirstOrder.Derives.imp_elim
          (is_relation_member_eq_ordered_pair_projections
            (Γ := Δ) relation member)
          hPredicate)
        hMembership
  have hCoordinates : Δ ⊢ₘ[relation_plane_theory]
      (left ∈ₘ double) ∧ₘ (right ∈ₘ double) := by
    simpa [left, right, double] using
      FirstOrder.Derives.imp_elim
        (FirstOrder.Derives.imp_elim
          (ordered_pair_coordinates_mem_double_union
            (Γ := Δ) relation member left right)
          hMembership)
        hRepresentation
  have hRepresentedSquare : Δ ⊢ₘ[relation_plane_theory]
      represented ∈ₘ square := by
    simpa [represented, square, double] using
      FirstOrder.Derives.imp_elim
        (FirstOrder.Derives.imp_elim
          (ordered_pair_mem_cartesian_product
            (Γ := Δ) double double left right)
          (FirstOrder.Derives.conj_elim_left hCoordinates))
        (FirstOrder.Derives.conj_elim_right hCoordinates)
  exact FirstOrder.Derives.iff_elim_right
    (membership_left_iff_of_equality
      member represented square hRepresentation)
    hRepresentedSquare

/-- 任意关系包含于其双重并集的平方。 -/
theorem is_relation_subset_double_union_square
    {free : SetContext} {Γ : Context signature free}
    (relation : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      is_relation_formula relation ⟶ₘ
        (relation ⊆ₘ
          (double_union_term relation ×ₘ
            double_union_term relation)) := by
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free :=
    is_relation_formula relation :: Γ
  apply subset_intro subset_theory_subset_relation_plane_theory
  apply FirstOrder.Derives.imp_intro
  let member : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest
      (σ := signature) (free := free) SetSort.set
  let Θ : Context signature (SetSort.set :: free) :=
    (member ∈ₘ relation.weakenFree SetSort.set) ::
      FreshVariable.extendContext SetSort.set Δ
  have hPredicate : Θ ⊢ₘ[relation_plane_theory]
      is_relation_formula (relation.weakenFree SetSort.set) :=
    FirstOrder.Derives.assumption (by
      simp [Θ, Δ, FreshVariable.extendContext])
  have hMembership : Θ ⊢ₘ[relation_plane_theory]
      member ∈ₘ relation.weakenFree SetSort.set :=
    FirstOrder.Derives.assumption List.mem_cons_self
  exact FirstOrder.Derives.imp_elim
    (FirstOrder.Derives.imp_elim
      (is_relation_member_mem_double_union_square
        (Γ := Θ) (relation.weakenFree SetSort.set) member)
      hPredicate)
    hMembership

/-! ## 关系平方见证 -/

/-- 双重并集及其平方作为关系界的结构化存在公式。 -/
def relation_square_witnesses {bound free : SetContext}
    (relation : SetTerm bound free) : SetFormula bound free :=
  let double : SetTerm bound (SetSort.set :: free) := .fvar .here
  let square : SetTerm bound (SetSort.set :: SetSort.set :: free) :=
    .fvar .here
  let double' := double.weakenFree SetSort.set
  let relation' :=
    (relation.weakenFree SetSort.set).weakenFree SetSort.set
  ((double' ≐ₘ double_union_term relation') ∧ₘ
    ((square ≐ₘ (double' ×ₘ double')) ∧ₘ
      (relation' ⊆ₘ square)))
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set

/-- 关系由双重并集平方所界定，两个规范项提供存在见证。 -/
theorem is_relation_implies_relation_square_witnesses
    {free : SetContext} {Γ : Context signature free}
    (relation : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      is_relation_formula relation ⟶ₘ
        relation_square_witnesses relation := by
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free :=
    is_relation_formula relation :: Γ
  let double : SetOpenTerm free := double_union_term relation
  let square : SetOpenTerm free := double ×ₘ double
  have hSubset : Δ ⊢ₘ[relation_plane_theory]
      relation ⊆ₘ square := by
    simpa [square, double] using FirstOrder.Derives.imp_elim
      (is_relation_subset_double_union_square
        (Γ := Δ) relation)
      (FirstOrder.Derives.assumption List.mem_cons_self)
  unfold relation_square_witnesses
  apply FirstOrder.Derives.exists_intro double
  rw [Formula.instantiateTop_abstractFreeTop,
    Formula.instantiateFreeTop_existsFreeTop]
  apply FirstOrder.Derives.exists_intro square
  rw [Formula.instantiateTop_abstractFreeTop]
  simpa [Formula.instantiateFreeTop, Formula.substituteFree,
    Substitution.free_map, Substitution.instantiateFreeTop,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.liftFree,
    VariableSubstitution.instantiateFreeTop,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId, double, square] using
    FirstOrder.Derives.conj_intro
      (Metatheory.Derives.equality_refl
        (T := relation_plane_theory) (Γ := Δ) double)
      (FirstOrder.Derives.conj_intro
        (Metatheory.Derives.equality_refl
          (T := relation_plane_theory) (Γ := Δ) square)
        hSubset)

/-! ## 关系成员反转 -/

/-- 关系成员反转后仍落在同一双重并集平方中。 -/
theorem is_relation_member_reverse_mem_double_union_square
    {free : SetContext} {Γ : Context signature free}
    (relation member : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      is_relation_formula relation ⟶ₘ
        ((member ∈ₘ relation) ⟶ₘ
          (member⁻¹ₘ ∈ₘ
            (double_union_term relation ×ₘ
              double_union_term relation))) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free :=
    (member ∈ₘ relation) :: is_relation_formula relation :: Γ
  let left : SetOpenTerm free := (member)₀ₘ
  let right : SetOpenTerm free := (member)₁ₘ
  let represented : SetOpenTerm free := ⟨left, right⟩ₘ
  let swapped : SetOpenTerm free := ⟨right, left⟩ₘ
  let double : SetOpenTerm free := double_union_term relation
  let square : SetOpenTerm free := double ×ₘ double
  let reverse : SetOpenTerm free := member⁻¹ₘ
  have hPredicate : Δ ⊢ₘ[relation_plane_theory]
      is_relation_formula relation :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hMembership : Δ ⊢ₘ[relation_plane_theory]
      member ∈ₘ relation :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hRepresentation : Δ ⊢ₘ[relation_plane_theory]
      member ≐ₘ represented := by
    simpa [left, right, represented] using
      FirstOrder.Derives.imp_elim
        (FirstOrder.Derives.imp_elim
          (is_relation_member_eq_ordered_pair_projections
            (Γ := Δ) relation member)
          hPredicate)
        hMembership
  have hMemberSquare : Δ ⊢ₘ[relation_plane_theory]
      member ∈ₘ square := by
    simpa [square, double] using
      FirstOrder.Derives.imp_elim
        (FirstOrder.Derives.imp_elim
          (is_relation_member_mem_double_union_square
            (Γ := Δ) relation member)
          hPredicate)
        hMembership
  have hRepresentedSquare : Δ ⊢ₘ[relation_plane_theory]
      represented ∈ₘ square :=
    FirstOrder.Derives.iff_elim_left
      (membership_left_iff_of_equality
        member represented square hRepresentation)
      hMemberSquare
  have hSwappedSquare : Δ ⊢ₘ[relation_plane_theory]
      swapped ∈ₘ square := by
    simpa [represented, swapped, square] using
      FirstOrder.Derives.iff_elim_left
        (ordered_pair_mem_square_iff_swap
          (Γ := Δ) double left right)
        hRepresentedSquare
  have hReverseEquality : Δ ⊢ₘ[relation_plane_theory]
      reverse ≐ₘ swapped := by
    simpa [reverse, swapped, left, right,
      ordered_pair_reverse_spec] using
      FirstOrder.Derives.theory_weaken
        ordered_pair_reverse_operator_theory_subset_relation_plane_theory
        (ordered_pair_reverse_term_spec_derives
          (Γ := Δ) member)
  exact FirstOrder.Derives.iff_elim_right
    (membership_left_iff_of_equality
      reverse swapped square hReverseEquality)
    hSwappedSquare

/-! ## 有序对反转的结构性质 -/

/-- 反转函数项始终是由原项两个投影交换后组成的规范有序对。 -/
theorem ordered_pair_reverse_is_ordered_pair
    {free : SetContext} {Γ : Context signature free}
    (pair : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      is_ordered_pair_formula pair⁻¹ₘ := by
  let left : SetOpenTerm free := (pair)₀ₘ
  let right : SetOpenTerm free := (pair)₁ₘ
  let reverse : SetOpenTerm free := pair⁻¹ₘ
  let swapped : SetOpenTerm free := ⟨right, left⟩ₘ
  have hEquality : Γ ⊢ₘ[relation_plane_theory]
      reverse ≐ₘ swapped := by
    simpa [left, right, reverse, swapped,
      ordered_pair_reverse_spec] using
      FirstOrder.Derives.theory_weaken
        ordered_pair_reverse_operator_theory_subset_relation_plane_theory
        (ordered_pair_reverse_term_spec_derives
          (Γ := Γ) pair)
  have hCondition : Γ ⊢ₘ[relation_plane_theory]
      is_ordered_pair_condition reverse :=
    is_ordered_pair_condition_intro
      reverse right left hEquality
  have hDefinition := FirstOrder.Derives.theory_weaken
    relation_function_theory_subset_relation_plane_theory
    (is_ordered_pair_definition_instance_derives
      (Γ := Γ) reverse)
  exact FirstOrder.Derives.iff_elim_right hDefinition hCondition

/-- 有序对与其反转具有相同的一元并集。 -/
theorem is_ordered_pair_implies_union_reverse_eq_union
    {free : SetContext} {Γ : Context signature free}
    (pair : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      is_ordered_pair_formula pair ⟶ₘ
        ((⋃ₘ pair) ≐ₘ (⋃ₘ pair⁻¹ₘ)) := by
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free := is_ordered_pair_formula pair :: Γ
  let left : SetOpenTerm free := (pair)₀ₘ
  let right : SetOpenTerm free := (pair)₁ₘ
  let represented : SetOpenTerm free := ⟨left, right⟩ₘ
  let swapped : SetOpenTerm free := ⟨right, left⟩ₘ
  let coordinates : SetOpenTerm free := {left, right}ₘ
  let swappedCoordinates : SetOpenTerm free := {right, left}ₘ
  let reverse : SetOpenTerm free := pair⁻¹ₘ
  have hPredicate : Δ ⊢ₘ[relation_plane_theory]
      is_ordered_pair_formula pair :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hRepresentation : Δ ⊢ₘ[relation_plane_theory]
      pair ≐ₘ represented := by
    simpa [left, right, represented] using
      FirstOrder.Derives.imp_elim
        (FirstOrder.Derives.theory_weaken
          right_projection_operator_theory_subset_relation_plane_theory
          (is_ordered_pair_eq_ordered_pair_projections
            (Γ := Δ) pair))
        hPredicate
  have hReverseEquality : Δ ⊢ₘ[relation_plane_theory]
      reverse ≐ₘ swapped := by
    simpa [left, right, reverse, swapped,
      ordered_pair_reverse_spec] using
      FirstOrder.Derives.theory_weaken
        ordered_pair_reverse_operator_theory_subset_relation_plane_theory
        (ordered_pair_reverse_term_spec_derives
          (Γ := Δ) pair)
  have hPairUnion : Δ ⊢ₘ[relation_plane_theory]
      (⋃ₘ pair) ≐ₘ (⋃ₘ represented) :=
    union_term_congr_of_equality pair represented hRepresentation
  have hReverseUnion : Δ ⊢ₘ[relation_plane_theory]
      (⋃ₘ reverse) ≐ₘ (⋃ₘ swapped) :=
    union_term_congr_of_equality reverse swapped hReverseEquality
  have hRepresentedUnion : Δ ⊢ₘ[relation_plane_theory]
      (⋃ₘ represented) ≐ₘ coordinates := by
    simpa [represented, coordinates, left, right] using
      (union_ordered_pair_term_eq_unordered_pair
        (Γ := Δ) left right)
  have hSwappedUnion : Δ ⊢ₘ[relation_plane_theory]
      (⋃ₘ swapped) ≐ₘ swappedCoordinates := by
    simpa [swapped, swappedCoordinates, left, right] using
      (union_ordered_pair_term_eq_unordered_pair
        (Γ := Δ) right left)
  have hCoordinateComm : Δ ⊢ₘ[relation_plane_theory]
      coordinates ≐ₘ swappedCoordinates := by
    simpa [coordinates, swappedCoordinates, left, right] using
      (unordered_pair_term_comm (Γ := Δ) left right)
  have hToCoordinates := Metatheory.Derives.equality_trans
    hPairUnion hRepresentedUnion
  have hToSwappedCoordinates := Metatheory.Derives.equality_trans
    hToCoordinates hCoordinateComm
  have hToSwapped := Metatheory.Derives.equality_trans
    hToSwappedCoordinates
    (Metatheory.Derives.equality_symm hSwappedUnion)
  have hToReverse := Metatheory.Derives.equality_trans
    hToSwapped (Metatheory.Derives.equality_symm hReverseUnion)
  simpa [reverse] using hToReverse

/-- 有序对反转后仍是有序对，且一元并集保持不变。 -/
theorem is_ordered_pair_reverse_and_union_invariant
    {free : SetContext} {Γ : Context signature free}
    (pair : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      is_ordered_pair_formula pair ⟶ₘ
        (is_ordered_pair_formula pair⁻¹ₘ ∧ₘ
          ((⋃ₘ pair) ≐ₘ (⋃ₘ pair⁻¹ₘ))) := by
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free := is_ordered_pair_formula pair :: Γ
  exact FirstOrder.Derives.conj_intro
    (ordered_pair_reverse_is_ordered_pair
      (Γ := Δ) pair)
    (FirstOrder.Derives.imp_elim
      (is_ordered_pair_implies_union_reverse_eq_union
        (Γ := Δ) pair)
      (FirstOrder.Derives.assumption List.mem_cons_self))

/-! ## 有序对刻画 -/

/-- 有序对谓词等价于存在两个坐标使其等于规范有序对。 -/
theorem is_ordered_pair_iff_exists_coordinates
    {free : SetContext} {Γ : Context signature free}
    (pair : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      is_ordered_pair_formula pair ↔ₘ
        is_ordered_pair_condition pair :=
  FirstOrder.Derives.theory_weaken
    relation_function_theory_subset_relation_plane_theory
    (is_ordered_pair_definition_instance_derives
      (Γ := Γ) pair)

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
