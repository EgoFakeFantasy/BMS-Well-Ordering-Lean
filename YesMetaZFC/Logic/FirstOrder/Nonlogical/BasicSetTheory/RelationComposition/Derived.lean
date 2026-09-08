import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.RelationComposition.Core

/-!
# 关系逆与关系复合：导出定理

本模块只保留数学上可复用的存在性、唯一性、点态规格、规范项规格与关系闭包。
分离 schema、闭公理实例化和 fresh 变量全部经内在类型接口处理，不再暴露旧式良构、
闭性、变量编号或兼容桥接。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-! ## 参数化分离实例 -/

/-- 关系逆分离 schema 可直接消费任意关系项与母集项。 -/
theorem relation_converse_separation_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (relation source : SetOpenTerm free) :
    Γ ⊢ₘ[relation_converse_theory]
      relation_converse_separation_exists relation source := by
  have hGeneric := SetPredicate.separation_exists_derives
    (Γ := Γ) (relation_converse_predicate relation) source
  have hLifted := FirstOrder.Derives.theory_weaken
    (T := (relation_converse_predicate relation).separation_theory)
    (U := relation_converse_theory)
    (by
      intro sentence hSentence
      rcases hSentence with rfl | hExtensionality
      · exact Or.inl ⟨free, relation, rfl⟩
      · exact Or.inr
          (extensionality_theory_subset_relation_plane_theory
            hExtensionality))
    hGeneric
  simpa only [relation_converse_separation_exists,
    relation_converse_separation_spec,
    SetPredicate.separation_exists, SetPredicate.separation_spec,
    SetPredicate.separation_condition,
    relation_converse_predicate_weakenFree_atNewest,
    FreshVariable.newest] using! hLifted

/-- 关系复合分离 schema 可直接消费任意两个关系项与母集项。 -/
theorem relation_composition_separation_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (first second source : SetOpenTerm free) :
    Γ ⊢ₘ[relation_composition_theory]
      relation_composition_separation_exists first second source := by
  have hGeneric := SetPredicate.separation_exists_derives
    (Γ := Γ) (relation_composition_predicate first second) source
  have hLifted := FirstOrder.Derives.theory_weaken
    (T := (relation_composition_predicate first second).separation_theory)
    (U := relation_composition_theory)
    (by
      intro sentence hSentence
      rcases hSentence with rfl | hExtensionality
      · exact Or.inl ⟨free, first, second, rfl⟩
      · exact Or.inr
          (relation_converse_theory_subset_relation_converse_operator_theory
            (relation_plane_theory_subset_relation_converse_theory
              (extensionality_theory_subset_relation_plane_theory
                hExtensionality))))
    hGeneric
  simpa only [relation_composition_separation_exists,
    relation_composition_separation_spec,
    SetPredicate.separation_exists, SetPredicate.separation_spec,
    SetPredicate.separation_condition,
    relation_composition_predicate_weakenFree_atNewest,
    FreshVariable.newest] using! hLifted

/-! ## 存在性与闭定义公理实例化 -/

/-- 任意集合都有按标准母集分离得到的关系逆候选。 -/
theorem relation_converse_exists_derives
    {free : SetContext} {Γ : Context signature free}
    (relation : SetOpenTerm free) :
    Γ ⊢ₘ[relation_converse_theory]
      relation_converse_exists relation := by
  simpa [relation_converse_exists,
    relation_converse_separation_exists,
    relation_converse_separation_spec,
    relation_converse_member_condition] using!
    (relation_converse_separation_instance_derives
      (Γ := Γ) relation (relation_converse_bound_term relation))

/-- 任意两个集合都有按标准母集分离得到的关系复合候选。 -/
theorem relation_composition_exists_derives
    {free : SetContext} {Γ : Context signature free}
    (first second : SetOpenTerm free) :
    Γ ⊢ₘ[relation_composition_theory]
      relation_composition_exists first second := by
  simpa [relation_composition_exists,
    relation_composition_separation_exists,
    relation_composition_separation_spec,
    relation_composition_member_condition] using!
    (relation_composition_separation_instance_derives
      (Γ := Γ) first second
      (relation_composition_bound_term first second))

/-- 关系逆函数符号定义公理可在任意两个集合项处实例化。 -/
theorem relation_converse_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (relation candidate : SetOpenTerm free) :
    Γ ⊢ₘ[relation_converse_operator_theory]
      relation_converse_definition_instance relation candidate := by
  let body : SetOpenFormula [SetSort.set, SetSort.set] :=
    relation_converse_definition_instance
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set])
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons candidate
      (VariableSubstitution.cons relation VariableSubstitution.empty)
  have hClosed :
      ([] : Context signature []) ⊢ₘ[relation_converse_operator_theory]
        Formula.fromSentence relation_converse_definition_axiom :=
    FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, relation_converse_definition_axiom,
    relation_converse_definition_instance, relation_converse_spec,
    relation_converse_member_condition,
    relation_converse_graph_condition, membership_specification,
    Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.liftFree,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId] using hInstance

/-- 关系复合函数符号定义公理可在任意三个集合项处实例化。 -/
theorem relation_composition_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (first second candidate : SetOpenTerm free) :
    Γ ⊢ₘ[relation_composition_operator_theory]
      relation_composition_definition_instance first second candidate := by
  let body : SetOpenFormula
      [SetSort.set, SetSort.set, SetSort.set] :=
    relation_composition_definition_instance
      (.fvar (.there (.there .here)) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons candidate
      (VariableSubstitution.cons second
        (VariableSubstitution.cons first VariableSubstitution.empty))
  have hClosed :
      ([] : Context signature []) ⊢ₘ[relation_composition_operator_theory]
        Formula.fromSentence relation_composition_definition_axiom :=
    FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, relation_composition_definition_axiom,
    relation_composition_definition_instance,
    relation_composition_spec, relation_composition_member_condition,
    relation_composition_graph_condition, membership_specification,
    Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.liftFree,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId] using hInstance

/-! ## 点态规格与唯一性 -/

/-- 关系逆规格在任意元素处给出精确成员条件。 -/
theorem relation_converse_spec_membership_iff
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (relation candidate element : SetOpenTerm free)
    (hSpec : Γ ⊢ₘ[T] relation_converse_spec relation candidate) :
    Γ ⊢ₘ[T]
      (element ∈ₘ candidate) ↔ₘ
        relation_converse_member_condition relation element := by
  have hAt := FirstOrder.Derives.forall_elim element hSpec
  simpa [relation_converse_spec, membership_specification,
    relation_converse_member_condition,
    relation_converse_graph_condition,
    Formula.instantiateFreeTop, Formula.substituteFree,
    Substitution.free_map, Substitution.instantiateFreeTop,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.liftFree,
    VariableSubstitution.instantiateFreeTop,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId] using hAt

/-- 关系复合规格在任意元素处给出精确成员条件。 -/
theorem relation_composition_spec_membership_iff
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (first second candidate element : SetOpenTerm free)
    (hSpec : Γ ⊢ₘ[T]
      relation_composition_spec first second candidate) :
    Γ ⊢ₘ[T]
      (element ∈ₘ candidate) ↔ₘ
        relation_composition_member_condition first second element := by
  have hAt := FirstOrder.Derives.forall_elim element hSpec
  simpa [relation_composition_spec, membership_specification,
    relation_composition_member_condition,
    relation_composition_graph_condition,
    Formula.instantiateFreeTop, Formula.substituteFree,
    Substitution.free_map, Substitution.instantiateFreeTop,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.liftFree,
    VariableSubstitution.instantiateFreeTop,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId] using hAt

/-- 同一关系的两个关系逆候选必相等。 -/
theorem relation_converse_unique
    {free : SetContext} {Γ : Context signature free}
    (relation first second : SetOpenTerm free) :
    Γ ⊢ₘ[extensionality_theory]
      relation_converse_spec relation first ⟶ₘ
        relation_converse_spec relation second ⟶ₘ
          (first ≐ₘ second) := by
  let element : SetOpenTerm (SetSort.set :: free) := .fvar .here
  let condition : SetOpenFormula (SetSort.set :: free) :=
    relation_converse_member_condition
      (relation.weakenFree SetSort.set) element
  simpa [relation_converse_spec, condition, element] using
    (membership_specification_unique
      (Γ := Γ) first second condition)

/-- 同一对参数的两个关系复合候选必相等。 -/
theorem relation_composition_unique
    {free : SetContext} {Γ : Context signature free}
    (first second left right : SetOpenTerm free) :
    Γ ⊢ₘ[extensionality_theory]
      relation_composition_spec first second left ⟶ₘ
        relation_composition_spec first second right ⟶ₘ
          (left ≐ₘ right) := by
  let element : SetOpenTerm (SetSort.set :: free) := .fvar .here
  let condition : SetOpenFormula (SetSort.set :: free) :=
    relation_composition_member_condition
      (first.weakenFree SetSort.set)
      (second.weakenFree SetSort.set) element
  simpa [relation_composition_spec, condition, element] using
    (membership_specification_unique
      (Γ := Γ) left right condition)

/-! ## 规范函数项 -/

/-- 在关系谓词背景下，规范关系逆项满足关系逆规格。 -/
theorem is_relation_converse_term_spec
    {free : SetContext} {Γ : Context signature free}
    (relation : SetOpenTerm free) :
    Γ ⊢ₘ[relation_converse_operator_theory]
      is_relation_formula relation ⟶ₘ
        relation_converse_spec relation (converseₘ(relation)) := by
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free := is_relation_formula relation :: Γ
  have hDefinition : Δ ⊢ₘ[relation_converse_operator_theory]
      relation_converse_definition_instance
        relation (converseₘ(relation)) :=
    FirstOrder.Derives.context_weaken_cons
      (relation_converse_definition_instance_derives
        (Γ := Γ) relation (converseₘ(relation)))
  have hRelation : Δ ⊢ₘ[relation_converse_operator_theory]
      is_relation_formula relation :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hGraph := FirstOrder.Derives.imp_elim hDefinition hRelation
  exact FirstOrder.Derives.iff_elim_left hGraph
    (Metatheory.Derives.equality_refl
      (T := relation_converse_operator_theory) (Γ := Δ)
      (converseₘ(relation)))

/-- 在两个关系谓词背景下，规范复合项满足关系复合规格。 -/
theorem are_relations_composition_term_spec
    {free : SetContext} {Γ : Context signature free}
    (first second : SetOpenTerm free) :
    Γ ⊢ₘ[relation_composition_operator_theory]
      (is_relation_formula first ∧ₘ is_relation_formula second) ⟶ₘ
        relation_composition_spec first second (second ∘ₘ first) := by
  apply FirstOrder.Derives.imp_intro
  let premise := is_relation_formula first ∧ₘ is_relation_formula second
  let Δ : Context signature free := premise :: Γ
  have hDefinition : Δ ⊢ₘ[relation_composition_operator_theory]
      relation_composition_definition_instance
        first second (second ∘ₘ first) :=
    FirstOrder.Derives.context_weaken_cons
      (relation_composition_definition_instance_derives
        (Γ := Γ) first second (second ∘ₘ first))
  have hPremise : Δ ⊢ₘ[relation_composition_operator_theory] premise :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hGraph := FirstOrder.Derives.imp_elim hDefinition hPremise
  exact FirstOrder.Derives.iff_elim_left hGraph
    (Metatheory.Derives.equality_refl
      (T := relation_composition_operator_theory) (Γ := Δ)
      (second ∘ₘ first))

/-! ## 关系闭包 -/

/-- 关系逆规格中的候选包含于值域与定义域的笛卡尔积。 -/
theorem relation_converse_spec_subset_product
    {free : SetContext} {Γ : Context signature free}
    (relation candidate : SetOpenTerm free) :
    Γ ⊢ₘ[relation_converse_theory]
      relation_converse_spec relation candidate ⟶ₘ
        (candidate ⊆ₘ relation_converse_bound_term relation) := by
  let element : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest
      (σ := signature) (free := free) SetSort.set
  let condition : SetOpenFormula (SetSort.set :: free) :=
    relation_converse_graph_condition
      (relation.weakenFree SetSort.set) element
  have hSubset := membership_specification_subset_source
    (Γ := Γ) candidate (relation_converse_bound_term relation) condition
  exact FirstOrder.Derives.theory_weaken
    (fun {_} hSentence =>
      relation_plane_theory_subset_relation_converse_theory
        (subset_theory_subset_relation_plane_theory hSentence))
    (by
      simpa [relation_converse_spec,
        relation_converse_member_condition, condition, element]
        using! hSubset)

/-- 关系复合规格中的候选包含于定义域与值域的笛卡尔积。 -/
theorem relation_composition_spec_subset_product
    {free : SetContext} {Γ : Context signature free}
    (first second candidate : SetOpenTerm free) :
    Γ ⊢ₘ[relation_composition_theory]
      relation_composition_spec first second candidate ⟶ₘ
        (candidate ⊆ₘ
          relation_composition_bound_term first second) := by
  let element : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest
      (σ := signature) (free := free) SetSort.set
  let condition : SetOpenFormula (SetSort.set :: free) :=
    relation_composition_graph_condition
      (first.weakenFree SetSort.set)
      (second.weakenFree SetSort.set) element
  have hSubset := membership_specification_subset_source
    (Γ := Γ) candidate
    (relation_composition_bound_term first second) condition
  exact FirstOrder.Derives.theory_weaken
    (fun {_} hSentence =>
      relation_plane_theory_subset_relation_composition_theory
        (subset_theory_subset_relation_plane_theory hSentence))
    (by
      simpa [relation_composition_spec,
        relation_composition_member_condition, condition, element]
        using! hSubset)

/-- 任意满足关系逆规格的候选都是关系。 -/
theorem relation_converse_spec_is_relation
    {free : SetContext} {Γ : Context signature free}
    (relation candidate : SetOpenTerm free) :
    Γ ⊢ₘ[relation_converse_theory]
      relation_converse_spec relation candidate ⟶ₘ
        is_relation_formula candidate := by
  apply FirstOrder.Derives.imp_intro
  let specification : SetOpenFormula free :=
    relation_converse_spec relation candidate
  let Δ : Context signature free := specification :: Γ
  have hSubset := FirstOrder.Derives.imp_elim
    (relation_converse_spec_subset_product
      (Γ := Δ) relation candidate)
    (FirstOrder.Derives.assumption List.mem_cons_self)
  have hRelation := FirstOrder.Derives.theory_weaken
    relation_plane_theory_subset_relation_converse_theory
    (subset_cartesian_product_is_relation
      (Γ := Δ) (ranₘ(relation)) (domₘ(relation)) candidate)
  exact FirstOrder.Derives.imp_elim hRelation hSubset

/-- 任意满足关系复合规格的候选都是关系。 -/
theorem relation_composition_spec_is_relation
    {free : SetContext} {Γ : Context signature free}
    (first second candidate : SetOpenTerm free) :
    Γ ⊢ₘ[relation_composition_theory]
      relation_composition_spec first second candidate ⟶ₘ
        is_relation_formula candidate := by
  apply FirstOrder.Derives.imp_intro
  let specification : SetOpenFormula free :=
    relation_composition_spec first second candidate
  let Δ : Context signature free := specification :: Γ
  have hSubset := FirstOrder.Derives.imp_elim
    (relation_composition_spec_subset_product
      (Γ := Δ) first second candidate)
    (FirstOrder.Derives.assumption List.mem_cons_self)
  have hRelation := FirstOrder.Derives.theory_weaken
    relation_plane_theory_subset_relation_composition_theory
    (subset_cartesian_product_is_relation
      (Γ := Δ) (domₘ(first)) (ranₘ(second)) candidate)
  exact FirstOrder.Derives.imp_elim hRelation hSubset

/-- 关系的规范逆项仍是关系。 -/
theorem is_relation_converse_is_relation
    {free : SetContext} {Γ : Context signature free}
    (relation : SetOpenTerm free) :
    Γ ⊢ₘ[relation_converse_operator_theory]
      is_relation_formula relation ⟶ₘ
        is_relation_formula (converseₘ(relation)) := by
  apply FirstOrder.Derives.imp_intro
  let predicate : SetOpenFormula free := is_relation_formula relation
  let Δ : Context signature free := predicate :: Γ
  have hPredicate : Δ ⊢ₘ[relation_converse_operator_theory] predicate :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hSpec := FirstOrder.Derives.imp_elim
    (FirstOrder.Derives.context_weaken_cons
      (is_relation_converse_term_spec (Γ := Γ) relation))
    hPredicate
  have hRelation := FirstOrder.Derives.theory_weaken
    relation_converse_theory_subset_relation_converse_operator_theory
    (relation_converse_spec_is_relation
      (Γ := Δ) relation (converseₘ(relation)))
  exact FirstOrder.Derives.imp_elim hRelation hSpec

/-- 两个关系的规范复合项仍是关系。 -/
theorem are_relations_composition_is_relation
    {free : SetContext} {Γ : Context signature free}
    (first second : SetOpenTerm free) :
    Γ ⊢ₘ[relation_composition_operator_theory]
      (is_relation_formula first ∧ₘ is_relation_formula second) ⟶ₘ
        is_relation_formula (second ∘ₘ first) := by
  apply FirstOrder.Derives.imp_intro
  let premise : SetOpenFormula free :=
    is_relation_formula first ∧ₘ is_relation_formula second
  let Δ : Context signature free := premise :: Γ
  have hPremise : Δ ⊢ₘ[relation_composition_operator_theory] premise :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hSpec := FirstOrder.Derives.imp_elim
    (FirstOrder.Derives.context_weaken_cons
      (are_relations_composition_term_spec
        (Γ := Γ) first second))
    hPremise
  have hRelation := FirstOrder.Derives.theory_weaken
    relation_composition_theory_subset_relation_composition_operator_theory
    (relation_composition_spec_is_relation
      (Γ := Δ) first second (second ∘ₘ first))
  exact FirstOrder.Derives.imp_elim hRelation hSpec

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
