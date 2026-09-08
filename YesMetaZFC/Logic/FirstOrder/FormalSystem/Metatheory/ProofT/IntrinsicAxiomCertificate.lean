import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.AxiomPresentation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicKernel

/-!
# 内在证明支撑公理的完整证书族

逐层复用原理论的 `insert`、`union` 和参数化分离公理族。
每层证书精确覆盖对应理论，不把理论成员命题装入证书，也不增加对象公理。
这些证书用于完整证明检查器的理论公理分支。
-/

namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT

open Nonlogical.BasicSetTheory

set_option autoImplicit false

namespace IntrinsicAxiomCertificate

def presentation_extensionality : AxiomPresentation extensionality_theory :=
  AxiomPresentation.singleton extensionality_axiom

def presentation_pairing : AxiomPresentation pairing_theory :=
  AxiomPresentation.insert pairing_axiom presentation_extensionality

def presentation_pairing_operator : AxiomPresentation pairing_operator_theory :=
  AxiomPresentation.insert pair_definition_axiom presentation_pairing

def presentation_union : AxiomPresentation union_theory :=
  AxiomPresentation.insert union_axiom presentation_extensionality

def presentation_union_operator : AxiomPresentation union_operator_theory :=
  AxiomPresentation.insert union_definition_axiom presentation_union

def presentation_binary_union_base : AxiomPresentation binary_union_base_theory :=
  AxiomPresentation.union presentation_pairing_operator presentation_union_operator

def presentation_binary_union_operator : AxiomPresentation binary_union_operator_theory :=
  AxiomPresentation.insert
      binary_union_definition_axiom
      presentation_binary_union_base

def presentation_successor_base : AxiomPresentation successor_base_theory :=
  presentation_binary_union_operator

def presentation_successor_operator : AxiomPresentation successor_operator_theory :=
  AxiomPresentation.insert successor_definition_axiom presentation_successor_base

def presentation_singleton_operator : AxiomPresentation singleton_operator_theory :=
  AxiomPresentation.insert singleton_definition_axiom presentation_pairing_operator

def presentation_ordered_pair_operator : AxiomPresentation ordered_pair_operator_theory :=
  AxiomPresentation.insert ordered_pair_definition_axiom presentation_singleton_operator

def presentation_relation_function : AxiomPresentation relation_function_theory :=
  AxiomPresentation.insert is_ordered_pair_definition_axiom presentation_ordered_pair_operator

def presentation_left_projection_operator : AxiomPresentation left_projection_operator_theory :=
  AxiomPresentation.insert left_projection_definition_axiom presentation_relation_function

def presentation_right_projection_operator : AxiomPresentation right_projection_operator_theory :=
  AxiomPresentation.insert right_projection_definition_axiom presentation_left_projection_operator

def presentation_relation_base : AxiomPresentation relation_base_theory :=
  AxiomPresentation.union presentation_right_projection_operator presentation_union_operator

def presentation_relation_predicate : AxiomPresentation relation_predicate_theory :=
  AxiomPresentation.insert is_relation_definition_axiom presentation_relation_base

def presentation_relation_domain : AxiomPresentation relation_domain_theory :=
  by
    refine AxiomPresentation.union ?_ presentation_relation_predicate
    apply AxiomPresentation.indexed
    intro free
    apply AxiomPresentation.indexed
    intro relation
    exact AxiomPresentation.singleton _

def presentation_relation_domain_operator : AxiomPresentation relation_domain_operator_theory :=
  AxiomPresentation.insert domain_definition_axiom presentation_relation_domain

def presentation_relation_range : AxiomPresentation relation_range_theory :=
  by
    refine AxiomPresentation.union ?_ presentation_relation_domain_operator
    apply AxiomPresentation.indexed
    intro free
    apply AxiomPresentation.indexed
    intro relation
    exact AxiomPresentation.singleton _

def presentation_relation_range_operator : AxiomPresentation relation_range_operator_theory :=
  AxiomPresentation.insert range_definition_axiom presentation_relation_range

def presentation_subset : AxiomPresentation subset_theory :=
  AxiomPresentation.insert subset_definition_axiom presentation_extensionality

def presentation_power_set : AxiomPresentation power_set_theory :=
  AxiomPresentation.insert power_set_axiom presentation_subset

def presentation_power_set_operator : AxiomPresentation power_set_operator_theory :=
  AxiomPresentation.insert power_set_definition_axiom presentation_power_set

def presentation_cartesian_product_base : AxiomPresentation cartesian_product_base_theory :=
  AxiomPresentation.union presentation_ordered_pair_operator
      (AxiomPresentation.union presentation_power_set_operator
        presentation_binary_union_operator)

def presentation_cartesian_product : AxiomPresentation cartesian_product_theory := by
  refine AxiomPresentation.union ?_ presentation_cartesian_product_base
  apply AxiomPresentation.indexed
  intro free
  apply AxiomPresentation.indexed
  intro left
  apply AxiomPresentation.indexed
  intro right
  exact AxiomPresentation.singleton _

def presentation_cartesian_product_operator : AxiomPresentation cartesian_product_operator_theory :=
  AxiomPresentation.insert cartesian_product_definition_axiom presentation_cartesian_product

def presentation_ordered_pair_reverse_operator : AxiomPresentation ordered_pair_reverse_operator_theory :=
  AxiomPresentation.insert ordered_pair_reverse_definition_axiom
      presentation_right_projection_operator

def presentation_relation_plane : AxiomPresentation relation_plane_theory :=
  AxiomPresentation.union presentation_relation_range_operator
      (AxiomPresentation.union presentation_cartesian_product_operator
        presentation_ordered_pair_reverse_operator)

def presentation_relation_converse : AxiomPresentation relation_converse_theory := by
  refine AxiomPresentation.union ?_ presentation_relation_plane
  apply AxiomPresentation.indexed
  intro free
  apply AxiomPresentation.indexed
  intro relation
  exact AxiomPresentation.singleton _

def presentation_relation_converse_operator : AxiomPresentation relation_converse_operator_theory :=
  AxiomPresentation.insert relation_converse_definition_axiom presentation_relation_converse

def presentation_relation_composition : AxiomPresentation relation_composition_theory := by
  refine AxiomPresentation.union ?_ presentation_relation_converse_operator
  apply AxiomPresentation.indexed
  intro free
  apply AxiomPresentation.indexed
  intro first
  apply AxiomPresentation.indexed
  intro second
  exact AxiomPresentation.singleton _

def presentation_relation_composition_operator : AxiomPresentation relation_composition_operator_theory :=
  AxiomPresentation.insert relation_composition_definition_axiom
      presentation_relation_composition

def presentation_equivalence_relation : AxiomPresentation equivalence_relation_theory :=
  AxiomPresentation.insert is_equivalence_relation_definition_axiom
      presentation_relation_composition_operator

def presentation_function_predicate : AxiomPresentation function_predicate_theory :=
  AxiomPresentation.insert is_function_definition_axiom presentation_equivalence_relation

def presentation_mapping_predicate : AxiomPresentation mapping_predicate_theory :=
  AxiomPresentation.insert is_mapping_definition_axiom presentation_function_predicate

def presentation_function_application : AxiomPresentation function_application_theory :=
  AxiomPresentation.insert function_application_definition_axiom presentation_mapping_predicate

def presentation_injective_predicate : AxiomPresentation injective_predicate_theory :=
  AxiomPresentation.insert is_injective_definition_axiom presentation_function_application

def presentation_surjective_predicate : AxiomPresentation surjective_predicate_theory :=
  AxiomPresentation.insert is_surjective_definition_axiom presentation_injective_predicate

def presentation_bijection_predicate : AxiomPresentation bijection_predicate_theory :=
  AxiomPresentation.insert is_bijection_definition_axiom presentation_surjective_predicate

def presentation_identity : AxiomPresentation identity_theory := by
  refine AxiomPresentation.union ?_ presentation_bijection_predicate
  apply AxiomPresentation.indexed
  intro free
  apply AxiomPresentation.indexed
  intro source
  exact AxiomPresentation.singleton _

def presentation_identity_operator : AxiomPresentation identity_operator_theory :=
  AxiomPresentation.insert identity_definition_axiom presentation_identity

def presentation_mapping_collection : AxiomPresentation mapping_collection_theory := by
  refine AxiomPresentation.union ?_ presentation_identity_operator
  apply AxiomPresentation.indexed
  intro free
  apply AxiomPresentation.indexed
  intro source
  apply AxiomPresentation.indexed
  intro target
  exact AxiomPresentation.singleton _

def presentation_mapping_collection_operator : AxiomPresentation mapping_collection_operator_theory :=
  AxiomPresentation.insert mapping_collection_definition_axiom presentation_mapping_collection

def presentation_transitive_set : AxiomPresentation transitive_set_theory :=
  AxiomPresentation.insert is_transitive_set_definition_axiom
      presentation_mapping_collection_operator

def presentation_membership_relation : AxiomPresentation membership_relation_theory :=
  AxiomPresentation.insert membership_relation_predicate.separation_axiom
      presentation_transitive_set

def presentation_membership_relation_operator : AxiomPresentation membership_relation_operator_theory :=
  AxiomPresentation.insert membership_relation_definition_axiom
      presentation_membership_relation

def presentation_linear_order : AxiomPresentation linear_order_theory :=
  AxiomPresentation.insert is_linear_order_definition_axiom
      presentation_membership_relation_operator

def presentation_order_isomorphism : AxiomPresentation order_isomorphism_theory :=
  AxiomPresentation.insert is_order_isomorphism_definition_axiom presentation_linear_order

def presentation_order_isomorphic : AxiomPresentation order_isomorphic_theory :=
  AxiomPresentation.insert is_order_isomorphic_definition_axiom presentation_order_isomorphism

def presentation_order_embedding : AxiomPresentation order_embedding_theory :=
  AxiomPresentation.insert is_order_embedding_definition_axiom presentation_order_isomorphic

def presentation_order_embeddable : AxiomPresentation order_embeddable_theory :=
  AxiomPresentation.insert is_order_embeddable_definition_axiom presentation_order_embedding

def presentation_natural_discrete_linear_order : AxiomPresentation natural_discrete_linear_order_theory :=
  AxiomPresentation.insert is_natural_discrete_linear_order_definition_axiom
      presentation_order_embeddable

def presentation_well_order : AxiomPresentation well_order_theory :=
  AxiomPresentation.insert well_order_definition_axiom
      presentation_natural_discrete_linear_order

def presentation_finite_ordinal : AxiomPresentation finite_ordinal_theory :=
  presentation_well_order

def presentation_relation_image_separation : AxiomPresentation relation_image_separation_theory :=
  AxiomPresentation.insert relation_image_separation_axiom presentation_finite_ordinal

def presentation_image_operator : AxiomPresentation image_operator_theory :=
  AxiomPresentation.insert image_definition_axiom presentation_relation_image_separation

def presentation_restriction_operator : AxiomPresentation restriction_operator_theory :=
  AxiomPresentation.insert restriction_definition_axiom presentation_image_operator

def presentation_minimum_linear_order : AxiomPresentation minimum_linear_order_theory :=
  AxiomPresentation.insert minimum_linear_order_definition_axiom presentation_restriction_operator

def presentation_minimum_natural_order : AxiomPresentation minimum_natural_order_theory :=
  AxiomPresentation.insert minimum_natural_order_definition_axiom presentation_minimum_linear_order

def presentation_order_operator : AxiomPresentation order_operator_theory :=
  AxiomPresentation.insert maximum_natural_order_definition_axiom presentation_minimum_natural_order

def presentation_minimum_difference : AxiomPresentation minimum_difference_theory :=
  AxiomPresentation.insert minimum_difference_definition_axiom presentation_order_operator

def presentation_index_order_separation : AxiomPresentation index_order_separation_theory := by
  refine AxiomPresentation.union ?_ presentation_minimum_difference
  apply AxiomPresentation.indexed
  intro free
  apply AxiomPresentation.indexed
  intro sourceRelation
  apply AxiomPresentation.indexed
  intro sourceCarrier
  apply AxiomPresentation.indexed
  intro targetRelation
  apply AxiomPresentation.indexed
  intro targetCarrier
  exact AxiomPresentation.singleton _

def presentation_index_order : AxiomPresentation index_order_theory :=
  AxiomPresentation.insert index_order_definition_axiom presentation_index_order_separation

def presentation_power_set_bijection_separation : AxiomPresentation power_set_bijection_separation_theory := by
  refine AxiomPresentation.union ?_ presentation_index_order
  apply AxiomPresentation.indexed
  intro free
  apply AxiomPresentation.indexed
  intro natural
  exact AxiomPresentation.singleton _

def presentation_power_set_bijection : AxiomPresentation power_set_bijection_theory :=
  AxiomPresentation.insert power_set_bijection_definition_axiom
      presentation_power_set_bijection_separation

def presentation_symmetric_difference_separation : AxiomPresentation symmetric_difference_separation_theory := by
  refine AxiomPresentation.union ?_ presentation_power_set_bijection
  apply AxiomPresentation.indexed
  intro free
  apply AxiomPresentation.indexed
  intro left
  apply AxiomPresentation.indexed
  intro right
  exact AxiomPresentation.singleton _

def presentation_symmetric_difference : AxiomPresentation symmetric_difference_theory :=
  AxiomPresentation.insert symmetric_difference_definition_axiom
      presentation_symmetric_difference_separation

def presentation_finite_predicate : AxiomPresentation finite_predicate_theory :=
  AxiomPresentation.insert is_finite_definition_axiom presentation_symmetric_difference

def presentation_equinumerous_predicate : AxiomPresentation equinumerous_predicate_theory :=
  AxiomPresentation.insert is_equinumerous_definition_axiom presentation_finite_predicate

def presentation_cardinality_leq_predicate : AxiomPresentation cardinality_leq_predicate_theory :=
  AxiomPresentation.insert cardinality_leq_definition_axiom
      presentation_equinumerous_predicate

def presentation_cardinality_strict_less_predicate : AxiomPresentation cardinality_strict_less_predicate_theory :=
  AxiomPresentation.insert cardinality_strict_less_definition_axiom
      presentation_cardinality_leq_predicate

def presentation_dedekind_finite_predicate : AxiomPresentation dedekind_finite_predicate_theory :=
  AxiomPresentation.insert is_dedekind_finite_definition_axiom
      presentation_cardinality_strict_less_predicate

def presentation_basic_finite : AxiomPresentation basic_finite_theory :=
  presentation_dedekind_finite_predicate

def presentation_infinity_axiom : AxiomPresentation infinity_axiom_theory :=
  AxiomPresentation.insert infinity_axiom presentation_basic_finite

def presentation_inductive_set : AxiomPresentation inductive_set_theory :=
  AxiomPresentation.insert is_inductive_set_definition_axiom presentation_infinity_axiom

def presentation_inductive_core_separation : AxiomPresentation inductive_core_separation_theory := by
  refine AxiomPresentation.union ?_ presentation_inductive_set
  apply AxiomPresentation.indexed
  intro free
  apply AxiomPresentation.indexed
  intro source
  exact AxiomPresentation.singleton _

def presentation_inductive_core : AxiomPresentation inductive_core_theory :=
  AxiomPresentation.insert inductive_core_definition_axiom
      presentation_inductive_core_separation

def presentation_infinity : AxiomPresentation infinity_theory :=
  AxiomPresentation.insert omega_definition_axiom presentation_inductive_core

def presentation_unbounded_subset : AxiomPresentation unbounded_subset_theory :=
  AxiomPresentation.insert unbounded_subset_definition_axiom presentation_infinity

def presentation_bounded_subset : AxiomPresentation bounded_subset_theory :=
  AxiomPresentation.insert bounded_subset_definition_axiom presentation_unbounded_subset

def presentation_natural_order_type : AxiomPresentation natural_order_type_theory :=
  AxiomPresentation.insert natural_order_type_definition_axiom presentation_bounded_subset

def presentation_natural_subset_type : AxiomPresentation natural_subset_type_theory :=
  AxiomPresentation.insert natural_subset_type_definition_axiom presentation_natural_order_type

def presentation_natural_set : AxiomPresentation natural_set_theory :=
  presentation_natural_subset_type

def presentation_natural_addition : AxiomPresentation natural_addition_theory :=
  AxiomPresentation.insert natural_addition_definition_axiom presentation_natural_set

def presentation_natural_multiplication : AxiomPresentation natural_multiplication_theory :=
  AxiomPresentation.insert natural_multiplication_definition_axiom
      presentation_natural_addition

def presentation_natural_exponentiation : AxiomPresentation natural_exponentiation_theory :=
  AxiomPresentation.insert natural_exponentiation_definition_axiom
      presentation_natural_multiplication

def presentation_godel_pairing_core : AxiomPresentation godel_pairing_core_theory :=
  AxiomPresentation.insert godel_pairing_definition_axiom
      presentation_natural_exponentiation

def presentation_natural_exponentiation_bound : AxiomPresentation natural_exponentiation_bound_theory :=
  AxiomPresentation.insert natural_exponentiation_index_bound_axiom
      (AxiomPresentation.insert natural_exponent_product_index_bound_axiom
        presentation_godel_pairing_core)

def presentation_natural_addition_bound : AxiomPresentation natural_addition_bound_theory :=
  AxiomPresentation.insert natural_addition_upper_bound_axiom
      (AxiomPresentation.insert natural_positive_left_addition_strict_bound_axiom
        (AxiomPresentation.insert natural_le_lt_transitivity_axiom
          (AxiomPresentation.insert natural_godel_pairing_coordinate_bound_axiom
            presentation_natural_exponentiation_bound)))

def presentation_formal_language_encoding : AxiomPresentation formal_language_encoding_theory :=
  AxiomPresentation.insert structural_syntax_definition_axiom
      (AxiomPresentation.union presentation_successor_operator presentation_natural_addition_bound)

def presentation_membership_irreflexive : AxiomPresentation membership_irreflexive_theory :=
  AxiomPresentation.singleton membership_irreflexive_axiom

def presentation_empty_set : AxiomPresentation empty_set_theory :=
  AxiomPresentation.insert (empty_predicate (free := [])).separation_axiom
      presentation_extensionality

def presentation_empty_set_symbol : AxiomPresentation empty_set_symbol_theory :=
  AxiomPresentation.insert empty_set_definition_axiom presentation_empty_set

def presentation_infinite_predicate : AxiomPresentation infinite_predicate_theory :=
  AxiomPresentation.insert is_infinite_definition_axiom presentation_natural_exponentiation

def presentation_countable_predicate : AxiomPresentation countable_predicate_theory :=
  AxiomPresentation.insert is_countable_definition_axiom presentation_infinite_predicate

def presentation_uncountable_predicate : AxiomPresentation uncountable_predicate_theory :=
  AxiomPresentation.insert is_uncountable_definition_axiom presentation_countable_predicate

def presentation_countably_infinite_predicate : AxiomPresentation countably_infinite_predicate_theory :=
  AxiomPresentation.insert is_countably_infinite_definition_axiom
      presentation_uncountable_predicate

def presentation_cardinality_classification : AxiomPresentation cardinality_classification_theory :=
  presentation_countably_infinite_predicate

def presentation_finite_sequence_space : AxiomPresentation finite_sequence_space_theory :=
  AxiomPresentation.insert finite_sequence_space_definition_axiom
      presentation_cardinality_classification

def presentation_recursive_sequence_space : AxiomPresentation recursive_sequence_space_theory :=
  AxiomPresentation.insert recursive_sequence_space_definition_axiom
      presentation_finite_sequence_space

def presentation_omega_recursive_sequence : AxiomPresentation omega_recursive_sequence_theory :=
  AxiomPresentation.insert omega_recursive_sequence_definition_axiom
      presentation_recursive_sequence_space

def presentation_natural_difference : AxiomPresentation natural_difference_theory :=
  AxiomPresentation.insert natural_difference_definition_axiom
      presentation_omega_recursive_sequence

def presentation_omega_pair_order : AxiomPresentation omega_pair_order_theory :=
  AxiomPresentation.insert omega_pair_less_definition_axiom presentation_natural_difference

def presentation_godel_pairing : AxiomPresentation godel_pairing_theory :=
  AxiomPresentation.insert godel_pairing_definition_axiom presentation_omega_pair_order

def presentation_natural_arithmetic : AxiomPresentation natural_arithmetic_theory :=
  presentation_godel_pairing

def presentation_transitive_closure_operator : AxiomPresentation transitive_closure_operator_theory :=
  AxiomPresentation.insert transitive_closure_definition_axiom presentation_natural_arithmetic

def presentation_finite_hierarchy_operator : AxiomPresentation finite_hierarchy_operator_theory :=
  AxiomPresentation.insert finite_hierarchy_definition_axiom presentation_transitive_closure_operator

def presentation_finite_universe_operator : AxiomPresentation finite_universe_operator_theory :=
  AxiomPresentation.insert finite_universe_definition_axiom presentation_finite_hierarchy_operator

def presentation_hereditarily_finite_predicate : AxiomPresentation hereditarily_finite_predicate_theory :=
  AxiomPresentation.insert hereditarily_finite_definition_axiom presentation_finite_universe_operator

def presentation_finite_subset_collection_separation : AxiomPresentation finite_subset_collection_separation_theory :=
  AxiomPresentation.insert finite_subset_collection_separation_axiom
      presentation_hereditarily_finite_predicate

def presentation_finite_subset_collection_operator : AxiomPresentation finite_subset_collection_operator_theory :=
  AxiomPresentation.insert finite_subset_collection_definition_axiom
      presentation_finite_subset_collection_separation

def presentation_hereditarily_finite : AxiomPresentation hereditarily_finite_theory :=
  presentation_finite_subset_collection_operator

def presentation_finite_sequence_concatenation : AxiomPresentation finite_sequence_concatenation_theory :=
  AxiomPresentation.insert finite_sequence_concatenation_definition_axiom presentation_hereditarily_finite

def presentation_nonempty_finite_sequence_space_separation : AxiomPresentation nonempty_finite_sequence_space_separation_theory :=
  AxiomPresentation.insert nonempty_finite_sequence_space_separation_axiom
      presentation_finite_sequence_concatenation

def presentation_nonempty_finite_sequence_space : AxiomPresentation nonempty_finite_sequence_space_theory :=
  AxiomPresentation.insert nonempty_finite_sequence_space_definition_axiom
      presentation_nonempty_finite_sequence_space_separation

def presentation_finite_sequence_flatten : AxiomPresentation finite_sequence_flatten_theory :=
  AxiomPresentation.insert finite_sequence_flatten_definition_axiom
      presentation_nonempty_finite_sequence_space

def presentation_finite_sequence_support : AxiomPresentation finite_sequence_support_theory :=
  AxiomPresentation.union presentation_membership_irreflexive <|
      AxiomPresentation.union presentation_empty_set_symbol <|
        AxiomPresentation.union presentation_successor_operator <|
          AxiomPresentation.union presentation_binary_union_operator <|
            AxiomPresentation.union presentation_ordered_pair_operator <|
              AxiomPresentation.union presentation_function_application <|
                AxiomPresentation.union presentation_finite_sequence_flatten
                  presentation_finite_sequence_space

def presentation_intrinsic_arithmetic_evaluation : AxiomPresentation intrinsic_arithmetic_evaluation_theory :=
  AxiomPresentation.union presentation_formal_language_encoding
      presentation_finite_sequence_support

def presentation_expression_encoding : AxiomPresentation expression_encoding_theory :=
  AxiomPresentation.union presentation_membership_irreflexive
      (AxiomPresentation.union
        (AxiomPresentation.insert free_variable_occurs_definition_axiom
          (AxiomPresentation.insert syntax_transform_definition_axiom
            presentation_formal_language_encoding))
        presentation_empty_set_symbol)

def presentation_propositional_axiom_schema : AxiomPresentation propositional_axiom_schema_theory :=
  AxiomPresentation.insert propositional_axiom_schema_definition_axiom
      presentation_expression_encoding

def presentation_quantifier_axiom_schema : AxiomPresentation quantifier_axiom_schema_theory :=
  AxiomPresentation.insert quantifier_axiom_schema_definition_axiom
      presentation_propositional_axiom_schema

def presentation_equality_axiom_schema : AxiomPresentation equality_axiom_schema_theory :=
  AxiomPresentation.insert equality_axiom_schema_definition_axiom
      presentation_quantifier_axiom_schema

def presentation_logical_axiom_code : AxiomPresentation logical_axiom_code_theory :=
  AxiomPresentation.insert logical_axiom_code_definition_axiom
      presentation_equality_axiom_schema

def presentation_logical_rule_encoding : AxiomPresentation logical_rule_encoding_theory :=
  AxiomPresentation.insert modus_ponens_definition_axiom
      presentation_logical_axiom_code

def presentation_related_symbol_semantics : AxiomPresentation related_symbol_semantics_theory :=
  AxiomPresentation.insert related_nonlogical_symbol_set_definition_axiom
      presentation_logical_rule_encoding

def presentation_related_syntax_semantics : AxiomPresentation related_syntax_semantics_theory :=
  AxiomPresentation.insert related_syntax_definition_axiom presentation_related_symbol_semantics

def presentation_structure_semantics : AxiomPresentation structure_semantics_theory :=
  AxiomPresentation.insert structure_definition_axiom presentation_related_syntax_semantics

def presentation_term_value_semantics : AxiomPresentation term_value_semantics_theory :=
  AxiomPresentation.insert (term_value_definition_axiom ∧ₘ term_list_value_definition_axiom)
      presentation_structure_semantics

def presentation_semantic_interpretation : AxiomPresentation semantic_interpretation_theory :=
  presentation_term_value_semantics

def presentation_intrinsic_syntax_carrier : AxiomPresentation intrinsic_syntax_carrier_theory :=
  AxiomPresentation.union (AxiomPresentation.union presentation_subset presentation_empty_set_symbol)
      presentation_semantic_interpretation

def presentation_intrinsic_proof_row : AxiomPresentation intrinsic_proof_row_theory :=
  AxiomPresentation.union presentation_intrinsic_syntax_carrier
      presentation_finite_sequence_support

def presentation_intrinsic_proof : AxiomPresentation intrinsic_proof_theory :=
  AxiomPresentation.union presentation_intrinsic_arithmetic_evaluation
      presentation_intrinsic_proof_row

end IntrinsicAxiomCertificate

/-- 完整内在支撑理论的公理证书表示。 -/
def intrinsic_proof_axiom_presentation : AxiomPresentation intrinsic_proof_theory :=
  IntrinsicAxiomCertificate.presentation_intrinsic_proof

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT
