import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Relation.Core

/-!
# 关系、定义域与值域：导出定理

本模块从共享坐标内核导出关系谓词、双重并集、定义域和值域合同。定义域和值域
只在理论嵌入处区分；存在性、唯一性与点态成员定理均复用同一参数化证明。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-! ## 定义公理实例化 -/

/-- 关系谓词定义公理可在任意集合项处实例化。 -/
theorem is_relation_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (relation : SetOpenTerm free) :
    Γ ⊢ₘ[relation_predicate_theory]
      is_relation_definition_instance relation := by
  let body : SetOpenFormula [SetSort.set] :=
    is_relation_definition_instance
      (FreshVariable.newest
        (σ := signature) (free := []) SetSort.set)
  let τ : VariableSubstitution signature [SetSort.set] [] free :=
    VariableSubstitution.cons relation VariableSubstitution.empty
  have hClosed :
      ([] : Context signature []) ⊢ₘ[relation_predicate_theory]
        Formula.fromSentence is_relation_definition_axiom :=
    FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, is_relation_definition_axiom,
    is_relation_definition_instance, is_relation_condition,
    Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.liftFree,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId,
    FreshVariable.newest] using! hInstance

/-- 定义域定义公理可在任意关系与候选项处实例化。 -/
theorem domain_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (relation candidate : SetOpenTerm free) :
    Γ ⊢ₘ[relation_domain_operator_theory]
      domain_definition_instance relation candidate := by
  let body : SetOpenFormula [SetSort.set, SetSort.set] :=
    domain_definition_instance
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set])
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons candidate
      (VariableSubstitution.cons relation VariableSubstitution.empty)
  have hClosed :
      ([] : Context signature []) ⊢ₘ[relation_domain_operator_theory]
        Formula.fromSentence domain_definition_axiom :=
    FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, domain_definition_axiom,
    domain_definition_instance, relation_domain_spec,
    relation_coordinate_spec, relation_coordinate_member_condition,
    relation_coordinate_projection_term, membership_specification,
    Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.liftFree,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId] using hInstance

/-- 值域定义公理可在任意关系与候选项处实例化。 -/
theorem range_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (relation candidate : SetOpenTerm free) :
    Γ ⊢ₘ[relation_range_operator_theory]
      range_definition_instance relation candidate := by
  let body : SetOpenFormula [SetSort.set, SetSort.set] :=
    range_definition_instance
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set])
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons candidate
      (VariableSubstitution.cons relation VariableSubstitution.empty)
  have hClosed :
      ([] : Context signature []) ⊢ₘ[relation_range_operator_theory]
        Formula.fromSentence range_definition_axiom :=
    FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, range_definition_axiom,
    range_definition_instance, relation_range_spec,
    relation_coordinate_spec, relation_coordinate_member_condition,
    relation_coordinate_projection_term, membership_specification,
    Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.liftFree,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId] using hInstance

/-! ## 关系谓词 -/

/-- 关系谓词等价于“每个成员都是有序对”。 -/
theorem is_relation_iff_condition
    {free : SetContext} {Γ : Context signature free}
    (relation : SetOpenTerm free) :
    Γ ⊢ₘ[relation_predicate_theory]
      is_relation_formula relation ↔ₘ is_relation_condition relation :=
  is_relation_definition_instance_derives (Γ := Γ) relation

/-- 若规范 fresh 成员都是有序对，则该集合满足关系谓词。 -/
theorem is_relation_intro
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (hRelationTheory : ∀ {sentence : SetSentence},
      relation_predicate_theory sentence → T sentence)
    (relation : SetOpenTerm free)
    (hPoint : FreshVariable.extendContext SetSort.set Γ ⊢ₘ[T]
      (FreshVariable.newest
          (σ := signature) (free := free) SetSort.set ∈ₘ
        relation.weakenFree SetSort.set) ⟶ₘ
      is_ordered_pair_formula
        (FreshVariable.newest
          (σ := signature) (free := free) SetSort.set)) :
    Γ ⊢ₘ[T] is_relation_formula relation := by
  have hCondition : Γ ⊢ₘ[T] is_relation_condition relation := by
    unfold is_relation_condition
    exact FirstOrder.Derives.forall_intro hPoint
  have hDefinition := FirstOrder.Derives.theory_weaken
    hRelationTheory
    (is_relation_definition_instance_derives (Γ := Γ) relation)
  exact FirstOrder.Derives.iff_elim_right hDefinition hCondition

/-- 关系的任意成员都满足有序对谓词。 -/
theorem is_relation_member_is_ordered_pair
    {free : SetContext} {Γ : Context signature free}
    (relation member : SetOpenTerm free) :
    Γ ⊢ₘ[relation_predicate_theory]
      is_relation_formula relation ⟶ₘ
        (member ∈ₘ relation) ⟶ₘ is_ordered_pair_formula member := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free :=
    (member ∈ₘ relation) :: is_relation_formula relation :: Γ
  have hDefinition : Δ ⊢ₘ[relation_predicate_theory]
      is_relation_definition_instance relation :=
    FirstOrder.Derives.context_weaken_cons
      (assumption := member ∈ₘ relation)
      (FirstOrder.Derives.context_weaken_cons
        (assumption := is_relation_formula relation)
        (is_relation_definition_instance_derives (Γ := Γ) relation))
  have hRelation : Δ ⊢ₘ[relation_predicate_theory]
      is_relation_formula relation :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hCondition := FirstOrder.Derives.iff_elim_left
    hDefinition hRelation
  have hAt := FirstOrder.Derives.forall_elim member hCondition
  have hMembership : Δ ⊢ₘ[relation_predicate_theory]
      member ∈ₘ relation :=
    FirstOrder.Derives.assumption (by simp [Δ])
  exact FirstOrder.Derives.imp_elim
    (by simpa [is_relation_condition] using! hAt) hMembership

/-! ## 双重并集 -/

/-- 双重并集项满足外层一元并集规格。 -/
theorem double_union_term_spec_derives
    {free : SetContext} {Γ : Context signature free}
    (relation : SetOpenTerm free) :
    Γ ⊢ₘ[relation_base_theory]
      union_spec (⋃ₘ relation) (double_union_term relation) :=
  FirstOrder.Derives.theory_weaken
    union_operator_theory_subset_relation_base_theory
    (union_term_spec_derives (Γ := Γ) (⋃ₘ relation))

/-- 双重并集成员关系等价于外层并集的存在见证规格。 -/
theorem double_union_member_iff
    {free : SetContext} {Γ : Context signature free}
    (relation element : SetOpenTerm free) :
    Γ ⊢ₘ[relation_base_theory]
      (element ∈ₘ double_union_term relation) ↔ₘ
        double_union_member_condition relation element :=
  union_spec_membership_iff (Γ := Γ)
    (⋃ₘ relation) (double_union_term relation) element
    (double_union_term_spec_derives (Γ := Γ) relation)

/-! ## 坐标分离与唯一性 -/

/-- 坐标规格在任意元素处的点态实例。 -/
theorem relation_coordinate_spec_membership_iff
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (coordinate : RelationCoordinate)
    (relation candidate element : SetOpenTerm free)
    (hSpec : Γ ⊢ₘ[T]
      relation_coordinate_spec coordinate relation candidate) :
    Γ ⊢ₘ[T]
      (element ∈ₘ candidate) ↔ₘ
        ((element ∈ₘ double_union_term relation) ∧ₘ
          relation_coordinate_member_condition
            coordinate relation element) := by
  have hAt := FirstOrder.Derives.forall_elim element hSpec
  cases coordinate <;>
    simpa [relation_coordinate_spec,
      relation_coordinate_member_condition,
      relation_coordinate_projection_term,
      membership_specification,
      Formula.instantiateFreeTop, Formula.substituteFree,
      Substitution.free_map, Substitution.instantiateFreeTop,
      Formula.substitute, Formula.substituteMapped,
      Term.substituteMapped, Arguments.substituteMapped,
      VariableSubstitution.liftFree,
      VariableSubstitution.instantiateFreeTop,
      VariableSubstitution.weakenBound,
      VariableSubstitution.boundId,
      VariableSubstitution.freeId] using hAt

/-- 定义域分离 schema 可直接消费任意关系参数与母集。 -/
theorem relation_domain_separation_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (relation source : SetOpenTerm free) :
    Γ ⊢ₘ[relation_domain_theory]
      relation_coordinate_separation_exists
        RelationCoordinate.domain relation source := by
  have hGeneric := SetPredicate.separation_exists_derives
    (Γ := Γ)
    (relation_coordinate_predicate RelationCoordinate.domain relation)
    source
  have hLifted := FirstOrder.Derives.theory_weaken
    (T := (relation_coordinate_predicate
      RelationCoordinate.domain relation).separation_theory)
    (U := relation_domain_theory)
    (by
      intro sentence hSentence
      rcases hSentence with rfl | hExtensionality
      · exact Or.inl ⟨free, relation, rfl⟩
      · exact Or.inr
          (relation_base_theory_subset_relation_predicate_theory
            (extensionality_theory_subset_relation_base_theory
              hExtensionality)))
    hGeneric
  simpa only [relation_coordinate_separation_exists,
    relation_coordinate_separation_spec,
    SetPredicate.separation_exists, SetPredicate.separation_spec,
    SetPredicate.separation_condition,
    relation_coordinate_predicate_weakenFree_atNewest,
    FreshVariable.newest] using! hLifted

/-- 值域分离 schema 可直接消费任意关系参数与母集。 -/
theorem relation_range_separation_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (relation source : SetOpenTerm free) :
    Γ ⊢ₘ[relation_range_theory]
      relation_coordinate_separation_exists
        RelationCoordinate.range relation source := by
  have hGeneric := SetPredicate.separation_exists_derives
    (Γ := Γ)
    (relation_coordinate_predicate RelationCoordinate.range relation)
    source
  have hLifted := FirstOrder.Derives.theory_weaken
    (T := (relation_coordinate_predicate
      RelationCoordinate.range relation).separation_theory)
    (U := relation_range_theory)
    (by
      intro sentence hSentence
      rcases hSentence with rfl | hExtensionality
      · exact Or.inl ⟨free, relation, rfl⟩
      · exact Or.inr
          (relation_base_theory_subset_relation_domain_operator_theory
            (extensionality_theory_subset_relation_base_theory
              hExtensionality)))
    hGeneric
  simpa only [relation_coordinate_separation_exists,
    relation_coordinate_separation_spec,
    SetPredicate.separation_exists, SetPredicate.separation_spec,
    SetPredicate.separation_condition,
    relation_coordinate_predicate_weakenFree_atNewest,
    FreshVariable.newest] using! hLifted

/-- 同一关系的同一坐标规格具有唯一结果。 -/
theorem relation_coordinate_unique
    {free : SetContext} {Γ : Context signature free}
    (coordinate : RelationCoordinate)
    (relation first second : SetOpenTerm free) :
    Γ ⊢ₘ[relation_base_theory]
      relation_coordinate_spec coordinate relation first ⟶ₘ
        relation_coordinate_spec coordinate relation second ⟶ₘ
          (first ≐ₘ second) := by
  let element : SetOpenTerm (SetSort.set :: free) := .fvar .here
  let condition : SetOpenFormula (SetSort.set :: free) :=
    (element ∈ₘ double_union_term
      (relation.weakenFree SetSort.set)) ∧ₘ
    relation_coordinate_member_condition coordinate
      (relation.weakenFree SetSort.set) element
  have hUnique := membership_specification_unique
    (Γ := Γ) first second condition
  exact FirstOrder.Derives.theory_weaken
    extensionality_theory_subset_relation_base_theory
    (by simpa [relation_coordinate_spec, condition, element] using hUnique)

/-! ## 定义域 -/

theorem relation_domain_spec_membership_iff
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (relation candidate element : SetOpenTerm free)
    (hSpec : Γ ⊢ₘ[T] relation_domain_spec relation candidate) :
    Γ ⊢ₘ[T]
      (element ∈ₘ candidate) ↔ₘ
        ((element ∈ₘ double_union_term relation) ∧ₘ
          relation_domain_member_condition relation element) :=
  relation_coordinate_spec_membership_iff
    RelationCoordinate.domain relation candidate element hSpec

/-- 任意集合都有按左投影筛选得到的定义域候选。 -/
theorem relation_domain_exists_derives
    {free : SetContext} {Γ : Context signature free}
    (relation : SetOpenTerm free) :
    Γ ⊢ₘ[relation_domain_theory] relation_domain_exists relation := by
  simpa [relation_domain_exists, relation_coordinate_exists,
    relation_coordinate_separation_exists,
    relation_coordinate_separation_spec] using!
    (relation_domain_separation_instance_derives
      (Γ := Γ) relation (double_union_term relation))

/-- 若给定集合是关系，则其定义域存在。 -/
theorem is_relation_implies_domain_exists
    {free : SetContext} {Γ : Context signature free}
    (relation : SetOpenTerm free) :
    Γ ⊢ₘ[relation_domain_theory]
      is_relation_formula relation ⟶ₘ relation_domain_exists relation := by
  apply FirstOrder.Derives.imp_intro
  exact FirstOrder.Derives.context_weaken_cons
    (relation_domain_exists_derives (Γ := Γ) relation)

/-- 同一关系的两个定义域候选必相等。 -/
theorem relation_domain_unique
    {free : SetContext} {Γ : Context signature free}
    (relation first second : SetOpenTerm free) :
    Γ ⊢ₘ[relation_base_theory]
      relation_domain_spec relation first ⟶ₘ
        relation_domain_spec relation second ⟶ₘ (first ≐ₘ second) :=
  relation_coordinate_unique RelationCoordinate.domain
    relation first second

/-- 关系谓词背景下定义域规格保持唯一。 -/
theorem is_relation_domain_unique
    {free : SetContext} {Γ : Context signature free}
    (relation first second : SetOpenTerm free) :
    Γ ⊢ₘ[relation_domain_theory]
      is_relation_formula relation ⟶ₘ
        relation_domain_spec relation first ⟶ₘ
          relation_domain_spec relation second ⟶ₘ (first ≐ₘ second) := by
  apply FirstOrder.Derives.imp_intro
  exact FirstOrder.Derives.context_weaken_cons
    (FirstOrder.Derives.theory_weaken
      relation_base_theory_subset_relation_domain_theory
      (relation_domain_unique (Γ := Γ) relation first second))

/-- 候选项等于 `dom`，当且仅当它满足定义域规格。 -/
theorem domain_eq_iff_spec
    {free : SetContext} {Γ : Context signature free}
    (relation candidate : SetOpenTerm free) :
    Γ ⊢ₘ[relation_domain_operator_theory]
      is_relation_formula relation ⟶ₘ
        ((candidate ≐ₘ domₘ(relation)) ↔ₘ
          relation_domain_spec relation candidate) :=
  domain_definition_instance_derives (Γ := Γ) relation candidate

/-- 关系谓词背景下，规范定义域项满足定义域规格。 -/
theorem is_relation_domain_term_spec
    {free : SetContext} {Γ : Context signature free}
    (relation : SetOpenTerm free) :
    Γ ⊢ₘ[relation_domain_operator_theory]
      is_relation_formula relation ⟶ₘ
        relation_domain_spec relation (domₘ(relation)) := by
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free := is_relation_formula relation :: Γ
  have hDefinition : Δ ⊢ₘ[relation_domain_operator_theory]
      domain_definition_instance relation (domₘ(relation)) :=
    FirstOrder.Derives.context_weaken_cons
      (domain_definition_instance_derives (Γ := Γ)
        relation (domₘ(relation)))
  have hRelation : Δ ⊢ₘ[relation_domain_operator_theory]
      is_relation_formula relation :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hGraph := FirstOrder.Derives.imp_elim hDefinition hRelation
  exact FirstOrder.Derives.iff_elim_left hGraph
    (Metatheory.Derives.equality_refl
      (T := relation_domain_operator_theory) (Γ := Δ)
      (domₘ(relation)))

/-- 关系谓词背景下，`dom` 的成员关系满足定义域规格。 -/
theorem is_relation_domain_member_iff
    {free : SetContext} {Γ : Context signature free}
    (relation element : SetOpenTerm free) :
    Γ ⊢ₘ[relation_domain_operator_theory]
      is_relation_formula relation ⟶ₘ
        ((element ∈ₘ domₘ(relation)) ↔ₘ
          ((element ∈ₘ double_union_term relation) ∧ₘ
            relation_domain_member_condition relation element)) := by
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free := is_relation_formula relation :: Γ
  have hSpec : Δ ⊢ₘ[relation_domain_operator_theory]
      relation_domain_spec relation (domₘ(relation)) :=
    FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.context_weaken_cons
        (is_relation_domain_term_spec (Γ := Γ) relation))
      (FirstOrder.Derives.assumption List.mem_cons_self)
  exact relation_domain_spec_membership_iff
    relation (domₘ(relation)) element hSpec

/-! ## 值域 -/

theorem relation_range_spec_membership_iff
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (relation candidate element : SetOpenTerm free)
    (hSpec : Γ ⊢ₘ[T] relation_range_spec relation candidate) :
    Γ ⊢ₘ[T]
      (element ∈ₘ candidate) ↔ₘ
        ((element ∈ₘ double_union_term relation) ∧ₘ
          relation_range_member_condition relation element) :=
  relation_coordinate_spec_membership_iff
    RelationCoordinate.range relation candidate element hSpec

/-- 任意集合都有按右投影筛选得到的值域候选。 -/
theorem relation_range_exists_derives
    {free : SetContext} {Γ : Context signature free}
    (relation : SetOpenTerm free) :
    Γ ⊢ₘ[relation_range_theory] relation_range_exists relation := by
  simpa [relation_range_exists, relation_coordinate_exists,
    relation_coordinate_separation_exists,
    relation_coordinate_separation_spec] using!
    (relation_range_separation_instance_derives
      (Γ := Γ) relation (double_union_term relation))

/-- 若给定集合是关系，则其值域存在。 -/
theorem is_relation_implies_range_exists
    {free : SetContext} {Γ : Context signature free}
    (relation : SetOpenTerm free) :
    Γ ⊢ₘ[relation_range_theory]
      is_relation_formula relation ⟶ₘ relation_range_exists relation := by
  apply FirstOrder.Derives.imp_intro
  exact FirstOrder.Derives.context_weaken_cons
    (relation_range_exists_derives (Γ := Γ) relation)

/-- 同一关系的两个值域候选必相等。 -/
theorem relation_range_unique
    {free : SetContext} {Γ : Context signature free}
    (relation first second : SetOpenTerm free) :
    Γ ⊢ₘ[relation_base_theory]
      relation_range_spec relation first ⟶ₘ
        relation_range_spec relation second ⟶ₘ (first ≐ₘ second) :=
  relation_coordinate_unique RelationCoordinate.range
    relation first second

/-- 关系谓词背景下值域规格保持唯一。 -/
theorem is_relation_range_unique
    {free : SetContext} {Γ : Context signature free}
    (relation first second : SetOpenTerm free) :
    Γ ⊢ₘ[relation_range_theory]
      is_relation_formula relation ⟶ₘ
        relation_range_spec relation first ⟶ₘ
          relation_range_spec relation second ⟶ₘ (first ≐ₘ second) := by
  apply FirstOrder.Derives.imp_intro
  exact FirstOrder.Derives.context_weaken_cons
    (FirstOrder.Derives.theory_weaken
      relation_base_theory_subset_relation_range_theory
      (relation_range_unique (Γ := Γ) relation first second))

/-- 候选项等于 `range`，当且仅当它满足值域规格。 -/
theorem range_eq_iff_spec
    {free : SetContext} {Γ : Context signature free}
    (relation candidate : SetOpenTerm free) :
    Γ ⊢ₘ[relation_range_operator_theory]
      is_relation_formula relation ⟶ₘ
        ((candidate ≐ₘ ranₘ(relation)) ↔ₘ
          relation_range_spec relation candidate) :=
  range_definition_instance_derives (Γ := Γ) relation candidate

/-- 关系谓词背景下，规范值域项满足值域规格。 -/
theorem is_relation_range_term_spec
    {free : SetContext} {Γ : Context signature free}
    (relation : SetOpenTerm free) :
    Γ ⊢ₘ[relation_range_operator_theory]
      is_relation_formula relation ⟶ₘ
        relation_range_spec relation (ranₘ(relation)) := by
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free := is_relation_formula relation :: Γ
  have hDefinition : Δ ⊢ₘ[relation_range_operator_theory]
      range_definition_instance relation (ranₘ(relation)) :=
    FirstOrder.Derives.context_weaken_cons
      (range_definition_instance_derives (Γ := Γ)
        relation (ranₘ(relation)))
  have hRelation : Δ ⊢ₘ[relation_range_operator_theory]
      is_relation_formula relation :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hGraph := FirstOrder.Derives.imp_elim hDefinition hRelation
  exact FirstOrder.Derives.iff_elim_left hGraph
    (Metatheory.Derives.equality_refl
      (T := relation_range_operator_theory) (Γ := Δ)
      (ranₘ(relation)))

/-- 关系谓词背景下，`range` 的成员关系满足值域规格。 -/
theorem is_relation_range_member_iff
    {free : SetContext} {Γ : Context signature free}
    (relation element : SetOpenTerm free) :
    Γ ⊢ₘ[relation_range_operator_theory]
      is_relation_formula relation ⟶ₘ
        ((element ∈ₘ ranₘ(relation)) ↔ₘ
          ((element ∈ₘ double_union_term relation) ∧ₘ
            relation_range_member_condition relation element)) := by
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free := is_relation_formula relation :: Γ
  have hSpec : Δ ⊢ₘ[relation_range_operator_theory]
      relation_range_spec relation (ranₘ(relation)) :=
    FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.context_weaken_cons
        (is_relation_range_term_spec (Γ := Γ) relation))
      (FirstOrder.Derives.assumption List.mem_cons_self)
  exact relation_range_spec_membership_iff
    relation (ranₘ(relation)) element hSpec

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
