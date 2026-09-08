import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SupportAssembly

/-! # 固定参数模板与实际分离外壳的代入交换律

先展开共同的分离外壳，再用变量像复合消去参数项周围的重命名与替换。
每类谓词只展开其自身固定构造，任意参数项保留为整体。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SupportAssembly
open Nonlogical.BasicSetTheory NatPacket SupportParameters
set_option autoImplicit false
attribute [local implicit_reducible] Kind.arity

section
attribute [local simp]
  SetPredicate.separation_open_axiom
  SetPredicate.separation_exists
  SetPredicate.separation_spec
  SetPredicate.separation_condition
  SetPredicate.atNewest
  SetPredicate.weakenFree
  membership_specification
  FreshVariable.newest
  Formula.substituteFree
  Substitution.free_map
  Formula.substitute
  Formula.substituteMapped
  Term.substituteMapped
  Arguments.substituteMapped
  VariableSubstitution.cons
  VariableSubstitution.freeId
  VariableSubstitution.boundId
  VariableSubstitution.liftFree
  VariableSubstitution.weakenBound
  Formula.abstractFreeTop
  Formula.forallFreeTop
  Formula.existsFreeTop
  Formula.instantiateTop
  Formula.weakenFree
  Formula.rename
  Renaming.weakenFree
  Renaming.free
  Formula.renameMapped
  Substitution.abstractFreeTop
  Substitution.instantiateTop
  VariableSubstitution.abstractBound
  VariableSubstitution.abstractFreeTop
  VariableSubstitution.instantiateTop
  VariableSubstitution.liftBound
  Term.newestFree
  membership_formula
  left_projection_term
  Term.renameMapped
  Arguments.renameMapped
  VariableRenaming.id
  VariableRenaming.weaken
  Variable.weaken
  VariableRenaming.lift
  SyntaxSubstitution.term_weakenFree_substitute
  SyntaxSubstitution.closed_term_substitute
  SyntaxSubstitution.term_rename_substitute
  Term.embedBoundClosed
  Term.renameFree
  Term.rename
  VariableRenaming.comp
  SyntaxSubstitution.closed_term_substitute_id
  SyntaxSubstitution.term_weakenBound_substitute
  right_projection_term
  ordered_pair_term
  ordered_pair_reverse_term
  mapping_collection_term
  cartesian_product_term
  power_set_term
  binary_union_term
  function_application_term
  is_mapping_formula
  is_inductive_set_formula

/-- 固定模板在任意项参数处的代入，精确恢复原族的开放分离公理。 -/
theorem instantiate_eq (kind : Kind) (parameters : SyntaxParameters.Parameters kind.arity) :
    instantiate kind parameters = openAxiom kind parameters := by
  rcases parameters with ⟨free, args⟩
  cases kind
  case domain =>
    cases args with | cons relation tail0 =>
    cases tail0
    change ((relation_coordinate_predicate .domain (.fvar .here : SetOpenTerm (List.replicate 1 SetSort.set))).separation_open_axiom).substituteFree
      (VariableSubstitution.cons relation VariableSubstitution.empty) =
      (relation_coordinate_predicate .domain relation).separation_open_axiom
    simp [relation_coordinate_predicate, relation_coordinate_member_condition, relation_coordinate_projection_term]
  case range =>
    cases args with | cons relation tail0 =>
    cases tail0
    change ((relation_coordinate_predicate .range (.fvar .here : SetOpenTerm (List.replicate 1 SetSort.set))).separation_open_axiom).substituteFree
      (VariableSubstitution.cons relation VariableSubstitution.empty) =
      (relation_coordinate_predicate .range relation).separation_open_axiom
    simp [relation_coordinate_predicate, relation_coordinate_member_condition, relation_coordinate_projection_term]
  case cartesianProduct =>
    cases args with | cons left tail0 =>
    cases tail0 with | cons right tail1 =>
    cases tail1
    change ((cartesian_product_predicate (.fvar .here : SetOpenTerm (List.replicate 2 SetSort.set)) (.fvar (.there .here) : SetOpenTerm (List.replicate 2 SetSort.set))).separation_open_axiom).substituteFree
      (VariableSubstitution.cons left (VariableSubstitution.cons right VariableSubstitution.empty)) =
      (cartesian_product_predicate left right).separation_open_axiom
    simp [cartesian_product_predicate, cartesian_product_member_condition]
  case converse =>
    cases args with | cons relation tail0 =>
    cases tail0
    change ((relation_converse_predicate (.fvar .here : SetOpenTerm (List.replicate 1 SetSort.set))).separation_open_axiom).substituteFree
      (VariableSubstitution.cons relation VariableSubstitution.empty) =
      (relation_converse_predicate relation).separation_open_axiom
    simp [relation_converse_predicate, relation_converse_graph_condition]
  case composition =>
    cases args with | cons first tail0 =>
    cases tail0 with | cons second tail1 =>
    cases tail1
    change ((relation_composition_predicate (.fvar .here : SetOpenTerm (List.replicate 2 SetSort.set)) (.fvar (.there .here) : SetOpenTerm (List.replicate 2 SetSort.set))).separation_open_axiom).substituteFree
      (VariableSubstitution.cons first (VariableSubstitution.cons second VariableSubstitution.empty)) =
      (relation_composition_predicate first second).separation_open_axiom
    simp [relation_composition_predicate, relation_composition_graph_condition]
  case identity =>
    cases args with | cons source tail0 =>
    cases tail0
    change ((identity_predicate (.fvar .here : SetOpenTerm (List.replicate 1 SetSort.set))).separation_open_axiom).substituteFree
      (VariableSubstitution.cons source VariableSubstitution.empty) =
      (identity_predicate source).separation_open_axiom
    simp [identity_predicate, identity_graph_condition]
  case mappingCollection =>
    cases args with | cons source tail0 =>
    cases tail0 with | cons target tail1 =>
    cases tail1
    change ((mapping_collection_predicate (.fvar .here : SetOpenTerm (List.replicate 2 SetSort.set)) (.fvar (.there .here) : SetOpenTerm (List.replicate 2 SetSort.set))).separation_open_axiom).substituteFree
      (VariableSubstitution.cons source (VariableSubstitution.cons target VariableSubstitution.empty)) =
      (mapping_collection_predicate source target).separation_open_axiom
    simp [mapping_collection_predicate]
  case indexOrder =>
    cases args with | cons sourceRelation tail0 =>
    cases tail0 with | cons sourceCarrier tail1 =>
    cases tail1 with | cons targetRelation tail2 =>
    cases tail2 with | cons targetCarrier tail3 =>
    cases tail3
    change ((index_order_predicate (.fvar .here : SetOpenTerm (List.replicate 4 SetSort.set)) (.fvar (.there .here) : SetOpenTerm (List.replicate 4 SetSort.set)) (.fvar (.there (.there .here)) : SetOpenTerm (List.replicate 4 SetSort.set)) (.fvar (.there (.there (.there .here))) : SetOpenTerm (List.replicate 4 SetSort.set))).separation_open_axiom).substituteFree
      (VariableSubstitution.cons sourceRelation (VariableSubstitution.cons sourceCarrier (VariableSubstitution.cons targetRelation (VariableSubstitution.cons targetCarrier VariableSubstitution.empty)))) =
      (index_order_predicate sourceRelation sourceCarrier targetRelation targetCarrier).separation_open_axiom
    simp [index_order_predicate, index_order_member_condition]
  case powerSetBijection =>
    cases args with | cons natural tail0 =>
    cases tail0
    change ((power_set_bijection_predicate (.fvar .here : SetOpenTerm (List.replicate 1 SetSort.set))).separation_open_axiom).substituteFree
      (VariableSubstitution.cons natural VariableSubstitution.empty) =
      (power_set_bijection_predicate natural).separation_open_axiom
    simp [power_set_bijection_predicate, power_set_bijection_member_condition, binary_value_set_term]
  case symmetricDifference =>
    cases args with | cons left tail0 =>
    cases tail0 with | cons right tail1 =>
    cases tail1
    change ((symmetric_difference_predicate (.fvar .here : SetOpenTerm (List.replicate 2 SetSort.set)) (.fvar (.there .here) : SetOpenTerm (List.replicate 2 SetSort.set))).separation_open_axiom).substituteFree
      (VariableSubstitution.cons left (VariableSubstitution.cons right VariableSubstitution.empty)) =
      (symmetric_difference_predicate left right).separation_open_axiom
    simp [symmetric_difference_predicate, symmetric_difference_member_condition]
  case inductiveCore =>
    cases args with | cons source tail0 =>
    cases tail0
    change ((inductive_core_predicate (.fvar .here : SetOpenTerm (List.replicate 1 SetSort.set))).separation_open_axiom).substituteFree
      (VariableSubstitution.cons source VariableSubstitution.empty) =
      (inductive_core_predicate source).separation_open_axiom
    simp [inductive_core_predicate, inductive_core_member_condition]

end

/-- 关闭模板代入结果，得到实际原公理的同一闭句。 -/
theorem close_instantiate (kind : Kind) (parameters : SyntaxParameters.Parameters kind.arity) :
    Metatheory.Formula.forall_close (instantiate kind parameters) = sentence kind parameters := by
  rw [instantiate_eq]
  rfl

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SupportAssembly
