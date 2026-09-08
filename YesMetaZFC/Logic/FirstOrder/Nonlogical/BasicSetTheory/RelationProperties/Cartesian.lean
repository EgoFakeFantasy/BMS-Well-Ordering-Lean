import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.RelationProperties.Core

/-!
# 关系平面的笛卡尔积与坐标性质

本模块从复合幂集母集逐层建立笛卡尔积成员合同，并以结构化存在消去抽取坐标。
所有项、公式与新鲜变量均由上下文索引保证合法。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-! ## 复合母集 -/

/-- 左侧成员生成的单点集包含于二元并。 -/
theorem singleton_subset_binary_union_left
    {free : SetContext} {Γ : Context signature free}
    (left right element : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      (element ∈ₘ left) ⟶ₘ ({element}ₘ ⊆ₘ (left ∪ₘ right)) := by
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free := (element ∈ₘ left) :: Γ
  have hElementLeft : Δ ⊢ₘ[relation_plane_theory]
      element ∈ₘ left :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hElementUnion := FirstOrder.Derives.imp_elim
    (mem_binary_union_left (Γ := Δ) left right element)
    hElementLeft
  exact FirstOrder.Derives.imp_elim
    (singleton_subset_of_mem
      (Γ := Δ) element (left ∪ₘ right))
    hElementUnion

/-- 两侧成员生成的无序对包含于二元并。 -/
theorem unordered_pair_subset_binary_union
    {free : SetContext} {Γ : Context signature free}
    (left right first second : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      (first ∈ₘ left) ⟶ₘ
        ((second ∈ₘ right) ⟶ₘ
          ({first, second}ₘ ⊆ₘ (left ∪ₘ right))) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free :=
    (second ∈ₘ right) :: (first ∈ₘ left) :: Γ
  have hFirstUnion := FirstOrder.Derives.imp_elim
    (mem_binary_union_left (Γ := Δ) left right first)
    (FirstOrder.Derives.assumption (by simp [Δ]))
  have hSecondUnion := FirstOrder.Derives.imp_elim
    (mem_binary_union_right (Γ := Δ) left right second)
    (FirstOrder.Derives.assumption (by simp [Δ]))
  exact FirstOrder.Derives.imp_elim
    (FirstOrder.Derives.imp_elim
      (unordered_pair_subset_of_members
        (Γ := Δ) first second (left ∪ₘ right))
      hFirstUnion)
    hSecondUnion

/-- 左侧成员生成的单点集属于二元并的幂集。 -/
theorem singleton_mem_power_set_binary_union
    {free : SetContext} {Γ : Context signature free}
    (left right element : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      (element ∈ₘ left) ⟶ₘ
        ({element}ₘ ∈ₘ power_set_binary_union_term left right) := by
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free := (element ∈ₘ left) :: Γ
  have hSubset := FirstOrder.Derives.imp_elim
    (singleton_subset_binary_union_left
      (Γ := Δ) left right element)
    (FirstOrder.Derives.assumption List.mem_cons_self)
  have hMembership := FirstOrder.Derives.theory_weaken
    cartesian_product_operator_theory_subset_relation_plane_theory
    (FirstOrder.Derives.theory_weaken
      cartesian_product_base_theory_subset_cartesian_product_operator_theory
      (mem_power_set_binary_union_term_iff_subset
        (Γ := Δ) left right {element}ₘ))
  exact FirstOrder.Derives.iff_elim_right hMembership hSubset

/-- 两侧成员生成的无序对属于二元并的幂集。 -/
theorem unordered_pair_mem_power_set_binary_union
    {free : SetContext} {Γ : Context signature free}
    (left right first second : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      (first ∈ₘ left) ⟶ₘ
        ((second ∈ₘ right) ⟶ₘ
          ({first, second}ₘ ∈ₘ
            power_set_binary_union_term left right)) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free :=
    (second ∈ₘ right) :: (first ∈ₘ left) :: Γ
  have hSubset := FirstOrder.Derives.imp_elim
    (FirstOrder.Derives.imp_elim
      (unordered_pair_subset_binary_union
        (Γ := Δ) left right first second)
      (FirstOrder.Derives.assumption (by simp [Δ])))
    (FirstOrder.Derives.assumption (by simp [Δ]))
  have hMembership := FirstOrder.Derives.theory_weaken
    cartesian_product_operator_theory_subset_relation_plane_theory
    (FirstOrder.Derives.theory_weaken
      cartesian_product_base_theory_subset_cartesian_product_operator_theory
      (mem_power_set_binary_union_term_iff_subset
        (Γ := Δ) left right {first, second}ₘ))
  exact FirstOrder.Derives.iff_elim_right hMembership hSubset

/-- 坐标分别属于两侧集合时，有序对包含于笛卡尔积的内层幂集。 -/
theorem ordered_pair_subset_power_set_binary_union
    {free : SetContext} {Γ : Context signature free}
    (left right first second : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      (first ∈ₘ left) ⟶ₘ
        ((second ∈ₘ right) ⟶ₘ
          (⟨first, second⟩ₘ ⊆ₘ
            power_set_binary_union_term left right)) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free :=
    (second ∈ₘ right) :: (first ∈ₘ left) :: Γ
  let singleton : SetOpenTerm free := {first}ₘ
  let pair : SetOpenTerm free := {first, second}ₘ
  let ordered : SetOpenTerm free := ⟨first, second⟩ₘ
  let power : SetOpenTerm free :=
    power_set_binary_union_term left right
  have hSpec : Δ ⊢ₘ[relation_plane_theory]
      pair_spec singleton pair ordered := by
    simpa [singleton, pair, ordered, ordered_pair_spec] using
      FirstOrder.Derives.theory_weaken
        ordered_pair_operator_theory_subset_relation_plane_theory
        (ordered_pair_term_spec_derives
          (Γ := Δ) first second)
  have hSingletonPower : Δ ⊢ₘ[relation_plane_theory]
      singleton ∈ₘ power := by
    simpa [singleton, power] using
      FirstOrder.Derives.imp_elim
        (singleton_mem_power_set_binary_union
          (Γ := Δ) left right first)
        (FirstOrder.Derives.assumption (by simp [Δ]))
  have hPairPower : Δ ⊢ₘ[relation_plane_theory]
      pair ∈ₘ power := by
    simpa [pair, power] using FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.imp_elim
        (unordered_pair_mem_power_set_binary_union
          (Γ := Δ) left right first second)
        (FirstOrder.Derives.assumption (by simp [Δ])))
      (FirstOrder.Derives.assumption (by simp [Δ]))
  exact FirstOrder.Derives.imp_elim
    (FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.imp_elim
        (pair_spec_implies_subset_of_members
          (Γ := Δ) singleton pair ordered power)
        hSpec)
      hSingletonPower)
    hPairPower

/-- 规范有序对属于笛卡尔积的标准母集。 -/
theorem ordered_pair_mem_cartesian_product_bound
    {free : SetContext} {Γ : Context signature free}
    (left right first second : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      (first ∈ₘ left) ⟶ₘ
        ((second ∈ₘ right) ⟶ₘ
          (⟨first, second⟩ₘ ∈ₘ
            cartesian_product_bound_term left right)) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free :=
    (second ∈ₘ right) :: (first ∈ₘ left) :: Γ
  have hSubset := FirstOrder.Derives.imp_elim
    (FirstOrder.Derives.imp_elim
      (ordered_pair_subset_power_set_binary_union
        (Γ := Δ) left right first second)
      (FirstOrder.Derives.assumption (by simp [Δ])))
    (FirstOrder.Derives.assumption (by simp [Δ]))
  have hMembership := FirstOrder.Derives.theory_weaken
    cartesian_product_operator_theory_subset_relation_plane_theory
    (FirstOrder.Derives.theory_weaken
      cartesian_product_base_theory_subset_cartesian_product_operator_theory
      (mem_cartesian_product_bound_term_iff_subset
        (Γ := Δ) left right ⟨first, second⟩ₘ))
  exact FirstOrder.Derives.iff_elim_right hMembership hSubset

/-! ## 规范有序对的坐标条件 -/

/-- 坐标成员事实直接生成笛卡尔积的坐标成员条件。 -/
theorem ordered_pair_cartesian_product_member_condition
    {free : SetContext} {Γ : Context signature free}
    (left right first second : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      (first ∈ₘ left) ⟶ₘ
        ((second ∈ₘ right) ⟶ₘ
          cartesian_product_member_condition
            left right ⟨first, second⟩ₘ) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free :=
    (second ∈ₘ right) :: (first ∈ₘ left) :: Γ
  unfold cartesian_product_member_condition
  apply FirstOrder.Derives.exists_intro first
  rw [Formula.instantiateTop_abstractFreeTop,
    Formula.instantiateFreeTop_existsFreeTop]
  apply FirstOrder.Derives.exists_intro second
  rw [Formula.instantiateTop_abstractFreeTop]
  simpa [Formula.instantiateFreeTop, Formula.substituteFree,
    Substitution.free_map, Substitution.instantiateFreeTop,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.liftFree,
    VariableSubstitution.instantiateFreeTop,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId] using
    FirstOrder.Derives.conj_intro
      (FirstOrder.Derives.assumption
        (T := relation_plane_theory) (Γ := Δ) (by simp [Δ]))
      (FirstOrder.Derives.conj_intro
        (FirstOrder.Derives.assumption
          (T := relation_plane_theory) (Γ := Δ) (by simp [Δ]))
        (Metatheory.Derives.equality_refl
          (T := relation_plane_theory) (Γ := Δ)
          ⟨first, second⟩ₘ))

/-- 规范有序对属于笛卡尔积的正向坐标合同。 -/
theorem ordered_pair_mem_cartesian_product
    {free : SetContext} {Γ : Context signature free}
    (left right first second : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      (first ∈ₘ left) ⟶ₘ
        ((second ∈ₘ right) ⟶ₘ
          (⟨first, second⟩ₘ ∈ₘ (left ×ₘ right))) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free :=
    (second ∈ₘ right) :: (first ∈ₘ left) :: Γ
  have hSpec : Δ ⊢ₘ[relation_plane_theory]
      cartesian_product_spec left right (left ×ₘ right) :=
    FirstOrder.Derives.theory_weaken
      cartesian_product_operator_theory_subset_relation_plane_theory
      (cartesian_product_term_spec_derives
        (Γ := Δ) left right)
  have hPoint := cartesian_product_spec_membership_iff
    left right (left ×ₘ right) ⟨first, second⟩ₘ hSpec
  have hBound := FirstOrder.Derives.imp_elim
    (FirstOrder.Derives.imp_elim
      (ordered_pair_mem_cartesian_product_bound
        (Γ := Δ) left right first second)
      (FirstOrder.Derives.assumption (by simp [Δ])))
    (FirstOrder.Derives.assumption (by simp [Δ]))
  have hCondition := FirstOrder.Derives.imp_elim
    (FirstOrder.Derives.imp_elim
      (ordered_pair_cartesian_product_member_condition
        (Γ := Δ) left right first second)
      (FirstOrder.Derives.assumption (by simp [Δ])))
    (FirstOrder.Derives.assumption (by simp [Δ]))
  exact FirstOrder.Derives.iff_elim_right hPoint
    (FirstOrder.Derives.conj_intro hBound hCondition)

/-! ## 坐标抽取 -/

/-- 规范有序对满足笛卡尔积成员条件时，其坐标分别属于左右集合。 -/
theorem ordered_pair_member_condition_implies_coordinates
    {free : SetContext} {Γ : Context signature free}
    (left right first second : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      cartesian_product_member_condition
          left right ⟨first, second⟩ₘ ⟶ₘ
        ((first ∈ₘ left) ∧ₘ (second ∈ₘ right)) := by
  apply FirstOrder.Derives.imp_intro
  let condition : SetOpenFormula free :=
    cartesian_product_member_condition
      left right ⟨first, second⟩ₘ
  let Δ : Context signature free := condition :: Γ
  have hCondition : Δ ⊢ₘ[relation_plane_theory] condition :=
    FirstOrder.Derives.assumption List.mem_cons_self
  unfold condition cartesian_product_member_condition at hCondition
  apply FirstOrder.Derives.exists_elim hCondition
  let leftCoordinate₁ : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest
      (σ := signature) (free := free) SetSort.set
  let left₁ : SetOpenTerm (SetSort.set :: free) :=
    left.weakenFree SetSort.set
  let right₁ : SetOpenTerm (SetSort.set :: free) :=
    right.weakenFree SetSort.set
  let first₁ : SetOpenTerm (SetSort.set :: free) :=
    first.weakenFree SetSort.set
  let second₁ : SetOpenTerm (SetSort.set :: free) :=
    second.weakenFree SetSort.set
  let leftCoordinate₂ : SetOpenTerm
      (SetSort.set :: SetSort.set :: free) :=
    leftCoordinate₁.weakenFree SetSort.set
  let rightCoordinate : SetOpenTerm
      (SetSort.set :: SetSort.set :: free) :=
    FreshVariable.newest
      (σ := signature) (free := SetSort.set :: free) SetSort.set
  let left₂ : SetOpenTerm (SetSort.set :: SetSort.set :: free) :=
    left₁.weakenFree SetSort.set
  let right₂ : SetOpenTerm (SetSort.set :: SetSort.set :: free) :=
    right₁.weakenFree SetSort.set
  let first₂ : SetOpenTerm (SetSort.set :: SetSort.set :: free) :=
    first₁.weakenFree SetSort.set
  let second₂ : SetOpenTerm (SetSort.set :: SetSort.set :: free) :=
    second₁.weakenFree SetSort.set
  let data : SetOpenFormula (SetSort.set :: SetSort.set :: free) :=
    (leftCoordinate₂ ∈ₘ left₂) ∧ₘ
      ((rightCoordinate ∈ₘ right₂) ∧ₘ
        (⟨first₂, second₂⟩ₘ ≐ₘ
          ⟨leftCoordinate₂, rightCoordinate⟩ₘ))
  let inner : SetOpenFormula (SetSort.set :: free) :=
    data.existsFreeTop SetSort.set
  apply FirstOrder.Derives.exists_elim
    (FirstOrder.Derives.assumption List.mem_cons_self)
  let Ω : Context signature
      (SetSort.set :: SetSort.set :: free) :=
    data :: FreshVariable.extendContext SetSort.set
      (inner :: FreshVariable.extendContext SetSort.set Δ)
  change Ω ⊢ₘ[relation_plane_theory]
    (first₂ ∈ₘ left₂) ∧ₘ (second₂ ∈ₘ right₂)
  have hData : Ω ⊢ₘ[relation_plane_theory] data :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hLeftCoordinate : Ω ⊢ₘ[relation_plane_theory]
      leftCoordinate₂ ∈ₘ left₂ :=
    FirstOrder.Derives.conj_elim_left hData
  have hRightCoordinate : Ω ⊢ₘ[relation_plane_theory]
      rightCoordinate ∈ₘ right₂ :=
    FirstOrder.Derives.conj_elim_left
      (FirstOrder.Derives.conj_elim_right hData)
  have hPairEquality : Ω ⊢ₘ[relation_plane_theory]
      ⟨first₂, second₂⟩ₘ ≐ₘ
        ⟨leftCoordinate₂, rightCoordinate⟩ₘ :=
    FirstOrder.Derives.conj_elim_right
      (FirstOrder.Derives.conj_elim_right hData)
  have hCoordinates := FirstOrder.Derives.iff_elim_left
    (FirstOrder.Derives.theory_weaken
      ordered_pair_operator_theory_subset_relation_plane_theory
      (ordered_pair_term_eq_iff_coordinates
        (Γ := Ω) first₂ second₂
        leftCoordinate₂ rightCoordinate))
    hPairEquality
  have hFirst := FirstOrder.Derives.iff_elim_right
    (membership_left_iff_of_equality first₂ leftCoordinate₂ left₂
      (FirstOrder.Derives.conj_elim_left hCoordinates))
    hLeftCoordinate
  have hSecond := FirstOrder.Derives.iff_elim_right
    (membership_left_iff_of_equality second₂ rightCoordinate right₂
      (FirstOrder.Derives.conj_elim_right hCoordinates))
    hRightCoordinate
  exact FirstOrder.Derives.conj_intro hFirst hSecond

/-- 规范有序对属于笛卡尔积，当且仅当坐标分别属于左右集合。 -/
theorem ordered_pair_mem_cartesian_product_iff_coordinates
    {free : SetContext} {Γ : Context signature free}
    (left right first second : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      (⟨first, second⟩ₘ ∈ₘ (left ×ₘ right)) ↔ₘ
        ((first ∈ₘ left) ∧ₘ (second ∈ₘ right)) := by
  have hSpec : Γ ⊢ₘ[relation_plane_theory]
      cartesian_product_spec left right (left ×ₘ right) :=
    FirstOrder.Derives.theory_weaken
      cartesian_product_operator_theory_subset_relation_plane_theory
      (cartesian_product_term_spec_derives
        (Γ := Γ) left right)
  have hPoint := cartesian_product_spec_membership_iff
    left right (left ×ₘ right) ⟨first, second⟩ₘ hSpec
  apply FirstOrder.Derives.iff_intro
  · let membership : SetOpenFormula free :=
      ⟨first, second⟩ₘ ∈ₘ (left ×ₘ right)
    let Δ : Context signature free := membership :: Γ
    have hData := FirstOrder.Derives.iff_elim_left
      (FirstOrder.Derives.context_weaken_cons hPoint)
      (FirstOrder.Derives.assumption List.mem_cons_self)
    exact FirstOrder.Derives.imp_elim
      (ordered_pair_member_condition_implies_coordinates
        (Γ := Δ) left right first second)
      (FirstOrder.Derives.conj_elim_right hData)
  · let coordinates : SetOpenFormula free :=
      (first ∈ₘ left) ∧ₘ (second ∈ₘ right)
    let Δ : Context signature free := coordinates :: Γ
    have hCoordinates : Δ ⊢ₘ[relation_plane_theory] coordinates :=
      FirstOrder.Derives.assumption List.mem_cons_self
    exact FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.imp_elim
        (ordered_pair_mem_cartesian_product
          (Γ := Δ) left right first second)
        (FirstOrder.Derives.conj_elim_left hCoordinates))
      (FirstOrder.Derives.conj_elim_right hCoordinates)

/-! ## 笛卡尔积的关系性 -/

/-- 笛卡尔积成员条件中的坐标见证直接给出有序对谓词。 -/
theorem cartesian_product_member_condition_implies_is_ordered_pair
    {free : SetContext} {Γ : Context signature free}
    (left right element : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      cartesian_product_member_condition left right element ⟶ₘ
        is_ordered_pair_formula element := by
  apply FirstOrder.Derives.imp_intro
  let condition : SetOpenFormula free :=
    cartesian_product_member_condition left right element
  let Δ : Context signature free := condition :: Γ
  have hCondition : Δ ⊢ₘ[relation_plane_theory] condition :=
    FirstOrder.Derives.assumption List.mem_cons_self
  unfold condition cartesian_product_member_condition at hCondition
  apply FirstOrder.Derives.exists_elim hCondition
  let leftCoordinate₁ : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest
      (σ := signature) (free := free) SetSort.set
  let left₁ : SetOpenTerm (SetSort.set :: free) :=
    left.weakenFree SetSort.set
  let right₁ : SetOpenTerm (SetSort.set :: free) :=
    right.weakenFree SetSort.set
  let element₁ : SetOpenTerm (SetSort.set :: free) :=
    element.weakenFree SetSort.set
  let leftCoordinate₂ : SetOpenTerm
      (SetSort.set :: SetSort.set :: free) :=
    leftCoordinate₁.weakenFree SetSort.set
  let rightCoordinate : SetOpenTerm
      (SetSort.set :: SetSort.set :: free) :=
    FreshVariable.newest
      (σ := signature) (free := SetSort.set :: free) SetSort.set
  let left₂ : SetOpenTerm (SetSort.set :: SetSort.set :: free) :=
    left₁.weakenFree SetSort.set
  let right₂ : SetOpenTerm (SetSort.set :: SetSort.set :: free) :=
    right₁.weakenFree SetSort.set
  let element₂ : SetOpenTerm (SetSort.set :: SetSort.set :: free) :=
    element₁.weakenFree SetSort.set
  let data : SetOpenFormula (SetSort.set :: SetSort.set :: free) :=
    (leftCoordinate₂ ∈ₘ left₂) ∧ₘ
      ((rightCoordinate ∈ₘ right₂) ∧ₘ
        (element₂ ≐ₘ ⟨leftCoordinate₂, rightCoordinate⟩ₘ))
  let inner : SetOpenFormula (SetSort.set :: free) :=
    data.existsFreeTop SetSort.set
  apply FirstOrder.Derives.exists_elim
    (FirstOrder.Derives.assumption List.mem_cons_self)
  let Ω : Context signature
      (SetSort.set :: SetSort.set :: free) :=
    data :: FreshVariable.extendContext SetSort.set
      (inner :: FreshVariable.extendContext SetSort.set Δ)
  change Ω ⊢ₘ[relation_plane_theory]
    is_ordered_pair_formula element₂
  have hData : Ω ⊢ₘ[relation_plane_theory] data :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hRepresentation : Ω ⊢ₘ[relation_plane_theory]
      element₂ ≐ₘ ⟨leftCoordinate₂, rightCoordinate⟩ₘ :=
    FirstOrder.Derives.conj_elim_right
      (FirstOrder.Derives.conj_elim_right hData)
  have hCoordinates := is_ordered_pair_condition_intro
    (T := relation_plane_theory) (Γ := Ω)
    element₂ leftCoordinate₂ rightCoordinate hRepresentation
  exact FirstOrder.Derives.iff_elim_right
    (FirstOrder.Derives.theory_weaken
      relation_function_theory_subset_relation_plane_theory
      (is_ordered_pair_definition_instance_derives
        (Γ := Ω) element₂)) hCoordinates

/-- 笛卡尔积的任意成员都是有序对。 -/
theorem cartesian_product_member_is_ordered_pair
    {free : SetContext} {Γ : Context signature free}
    (left right element : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      (element ∈ₘ (left ×ₘ right)) ⟶ₘ
        is_ordered_pair_formula element := by
  apply FirstOrder.Derives.imp_intro
  let membership : SetOpenFormula free := element ∈ₘ (left ×ₘ right)
  let Δ : Context signature free := membership :: Γ
  have hSpec : Δ ⊢ₘ[relation_plane_theory]
      cartesian_product_spec left right (left ×ₘ right) :=
    FirstOrder.Derives.theory_weaken
      cartesian_product_operator_theory_subset_relation_plane_theory
      (cartesian_product_term_spec_derives
        (Γ := Δ) left right)
  have hPoint := cartesian_product_spec_membership_iff
    left right (left ×ₘ right) element hSpec
  have hData := FirstOrder.Derives.iff_elim_left hPoint
    (FirstOrder.Derives.assumption List.mem_cons_self)
  exact FirstOrder.Derives.imp_elim
    (cartesian_product_member_condition_implies_is_ordered_pair
      (Γ := Δ) left right element)
    (FirstOrder.Derives.conj_elim_right hData)

/-- 任意两个集合的笛卡尔积都是关系。 -/
theorem cartesian_product_is_relation
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      is_relation_formula (left ×ₘ right) := by
  apply is_relation_intro
    relation_predicate_theory_subset_relation_plane_theory
  simpa using
    (cartesian_product_member_is_ordered_pair
      (Γ := FreshVariable.extendContext SetSort.set Γ)
      (left.weakenFree SetSort.set)
      (right.weakenFree SetSort.set)
      (FreshVariable.newest
        (σ := signature) (free := free) SetSort.set))

/-- 任意笛卡尔积子集都是关系。 -/
theorem subset_cartesian_product_is_relation
    {free : SetContext} {Γ : Context signature free}
    (left right candidate : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      (candidate ⊆ₘ (left ×ₘ right)) ⟶ₘ
        is_relation_formula candidate := by
  apply FirstOrder.Derives.imp_intro
  let subsetFormula : SetOpenFormula free :=
    candidate ⊆ₘ (left ×ₘ right)
  let Δ : Context signature free := subsetFormula :: Γ
  have hProduct : Δ ⊢ₘ[relation_plane_theory]
      is_relation_formula (left ×ₘ right) :=
    cartesian_product_is_relation (Γ := Δ) left right
  have hSubset : Δ ⊢ₘ[relation_plane_theory] subsetFormula :=
    FirstOrder.Derives.assumption List.mem_cons_self
  exact FirstOrder.Derives.imp_elim
    (FirstOrder.Derives.imp_elim
      (is_relation_of_subset
        (Γ := Δ) (left ×ₘ right) candidate)
      hProduct)
    hSubset

/-- 同一平方中的规范有序对对坐标交换封闭。 -/
theorem ordered_pair_mem_square_iff_swap
    {free : SetContext} {Γ : Context signature free}
    (source first second : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      (⟨first, second⟩ₘ ∈ₘ (source ×ₘ source)) ↔ₘ
        (⟨second, first⟩ₘ ∈ₘ (source ×ₘ source)) := by
  have hForward := ordered_pair_mem_cartesian_product_iff_coordinates
    (Γ := Γ) source source first second
  have hBackward := ordered_pair_mem_cartesian_product_iff_coordinates
    (Γ := Γ) source source second first
  let firstCoordinates : SetOpenFormula free :=
    (first ∈ₘ source) ∧ₘ (second ∈ₘ source)
  let secondCoordinates : SetOpenFormula free :=
    (second ∈ₘ source) ∧ₘ (first ∈ₘ source)
  have hSwap : Γ ⊢ₘ[relation_plane_theory]
      firstCoordinates ↔ₘ secondCoordinates := by
    apply FirstOrder.Derives.iff_intro
    · have hCoordinates := FirstOrder.Derives.assumption
        (T := relation_plane_theory)
        (Γ := firstCoordinates :: Γ) List.mem_cons_self
      exact FirstOrder.Derives.conj_intro
        (FirstOrder.Derives.conj_elim_right hCoordinates)
        (FirstOrder.Derives.conj_elim_left hCoordinates)
    · have hCoordinates := FirstOrder.Derives.assumption
        (T := relation_plane_theory)
        (Γ := secondCoordinates :: Γ) List.mem_cons_self
      exact FirstOrder.Derives.conj_intro
        (FirstOrder.Derives.conj_elim_right hCoordinates)
        (FirstOrder.Derives.conj_elim_left hCoordinates)
  exact Metatheory.Derives.iff_trans
    (Metatheory.Derives.iff_trans
      (by simpa [firstCoordinates] using hForward) hSwap)
    (Metatheory.Derives.iff_symm
      (by simpa [secondCoordinates] using hBackward))

/-! ## 关系成员的双重并集坐标界 -/

/-- 一个关系成员按规范有序对表示时，两个坐标都属于关系的双重并集。 -/
theorem ordered_pair_coordinates_mem_double_union
    {free : SetContext} {Γ : Context signature free}
    (relation member first second : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      (member ∈ₘ relation) ⟶ₘ
        ((member ≐ₘ ⟨first, second⟩ₘ) ⟶ₘ
          ((first ∈ₘ double_union_term relation) ∧ₘ
            (second ∈ₘ double_union_term relation))) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  let membership : SetOpenFormula free := member ∈ₘ relation
  let representation : SetOpenFormula free :=
    member ≐ₘ ⟨first, second⟩ₘ
  let Δ : Context signature free := representation :: membership :: Γ
  let singleton : SetOpenTerm free := {first}ₘ
  let pair : SetOpenTerm free := {first, second}ₘ
  let ordered : SetOpenTerm free := ⟨first, second⟩ₘ
  have hMembership : Δ ⊢ₘ[relation_plane_theory] membership :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hRepresentation : Δ ⊢ₘ[relation_plane_theory]
      member ≐ₘ ordered := by
    simpa [ordered, representation] using
      (FirstOrder.Derives.assumption
        (T := relation_plane_theory) (Γ := Δ)
        (by simp [Δ, representation]))
  have hSingletonOrdered : Δ ⊢ₘ[relation_plane_theory]
      singleton ∈ₘ ordered := by
    simpa [singleton, ordered] using
      (singleton_mem_ordered_pair
        (Γ := Δ) first second)
  have hPairOrdered : Δ ⊢ₘ[relation_plane_theory]
      pair ∈ₘ ordered := by
    simpa [pair, ordered] using
      (unordered_pair_mem_ordered_pair
        (Γ := Δ) first second)
  have hSingletonMember : Δ ⊢ₘ[relation_plane_theory]
      singleton ∈ₘ member :=
    FirstOrder.Derives.iff_elim_right
      (membership_right_iff_of_equality
        singleton member ordered hRepresentation)
      hSingletonOrdered
  have hPairMember : Δ ⊢ₘ[relation_plane_theory]
      pair ∈ₘ member :=
    FirstOrder.Derives.iff_elim_right
      (membership_right_iff_of_equality
        pair member ordered hRepresentation)
      hPairOrdered
  have hSingletonUnion : Δ ⊢ₘ[relation_plane_theory]
      singleton ∈ₘ ⋃ₘ relation :=
    FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.imp_elim
        (mem_union_of_mem_of_mem
          (Γ := Δ) relation member singleton)
        hMembership)
      hSingletonMember
  have hPairUnion : Δ ⊢ₘ[relation_plane_theory]
      pair ∈ₘ ⋃ₘ relation :=
    FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.imp_elim
        (mem_union_of_mem_of_mem
          (Γ := Δ) relation member pair)
        hMembership)
      hPairMember
  have hFirstSingleton : Δ ⊢ₘ[relation_plane_theory]
      first ∈ₘ singleton := by
    simpa [singleton] using
      (mem_singleton_self (Γ := Δ) first)
  have hSecondPair : Δ ⊢ₘ[relation_plane_theory]
      second ∈ₘ pair := by
    simpa [pair] using
      (mem_unordered_pair_right
        (Γ := Δ) first second)
  have hFirstDouble : Δ ⊢ₘ[relation_plane_theory]
      first ∈ₘ double_union_term relation := by
    exact FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.imp_elim
        (mem_union_of_mem_of_mem
          (Γ := Δ) (⋃ₘ relation) singleton first)
        hSingletonUnion)
      hFirstSingleton
  have hSecondDouble : Δ ⊢ₘ[relation_plane_theory]
      second ∈ₘ double_union_term relation := by
    exact FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.imp_elim
        (mem_union_of_mem_of_mem
          (Γ := Δ) (⋃ₘ relation) pair second)
        hPairUnion)
      hSecondPair
  exact FirstOrder.Derives.conj_intro hFirstDouble hSecondDouble

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
