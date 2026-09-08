import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicAxiomCertificate
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.AxiomDecode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SyntaxDecode

/-! # 全部内在支撑公理分支的正向解码

与公理呈现逐层对应；参数化分离族显式解析上下文及所有项参数。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT
open Nonlogical.BasicSetTheory
set_option autoImplicit false
namespace IntrinsicAxiomDecode

def decode_extensionality : AxiomDecoder IntrinsicAxiomCertificate.presentation_extensionality :=
  AxiomDecoder.singleton extensionality_axiom

def decode_pairing : AxiomDecoder IntrinsicAxiomCertificate.presentation_pairing :=
  AxiomDecoder.insert pairing_axiom decode_extensionality

def decode_pairing_operator : AxiomDecoder IntrinsicAxiomCertificate.presentation_pairing_operator :=
  AxiomDecoder.insert pair_definition_axiom decode_pairing

def decode_union : AxiomDecoder IntrinsicAxiomCertificate.presentation_union :=
  AxiomDecoder.insert union_axiom decode_extensionality

def decode_union_operator : AxiomDecoder IntrinsicAxiomCertificate.presentation_union_operator :=
  AxiomDecoder.insert union_definition_axiom decode_union

def decode_binary_union_base : AxiomDecoder IntrinsicAxiomCertificate.presentation_binary_union_base :=
  AxiomDecoder.union decode_pairing_operator decode_union_operator

def decode_binary_union_operator : AxiomDecoder IntrinsicAxiomCertificate.presentation_binary_union_operator :=
  AxiomDecoder.insert
      binary_union_definition_axiom
      decode_binary_union_base

def decode_successor_base : AxiomDecoder IntrinsicAxiomCertificate.presentation_successor_base :=
  decode_binary_union_operator

def decode_successor_operator : AxiomDecoder IntrinsicAxiomCertificate.presentation_successor_operator :=
  AxiomDecoder.insert successor_definition_axiom decode_successor_base

def decode_singleton_operator : AxiomDecoder IntrinsicAxiomCertificate.presentation_singleton_operator :=
  AxiomDecoder.insert singleton_definition_axiom decode_pairing_operator

def decode_ordered_pair_operator : AxiomDecoder IntrinsicAxiomCertificate.presentation_ordered_pair_operator :=
  AxiomDecoder.insert ordered_pair_definition_axiom decode_singleton_operator

def decode_relation_function : AxiomDecoder IntrinsicAxiomCertificate.presentation_relation_function :=
  AxiomDecoder.insert is_ordered_pair_definition_axiom decode_ordered_pair_operator

def decode_left_projection_operator : AxiomDecoder IntrinsicAxiomCertificate.presentation_left_projection_operator :=
  AxiomDecoder.insert left_projection_definition_axiom decode_relation_function

def decode_right_projection_operator : AxiomDecoder IntrinsicAxiomCertificate.presentation_right_projection_operator :=
  AxiomDecoder.insert right_projection_definition_axiom decode_left_projection_operator

def decode_relation_base : AxiomDecoder IntrinsicAxiomCertificate.presentation_relation_base :=
  AxiomDecoder.union decode_right_projection_operator decode_union_operator

def decode_relation_predicate : AxiomDecoder IntrinsicAxiomCertificate.presentation_relation_predicate :=
  AxiomDecoder.insert is_relation_definition_axiom decode_relation_base

def decode_relation_domain : AxiomDecoder IntrinsicAxiomCertificate.presentation_relation_domain :=
  by
    refine AxiomDecoder.union ?_ decode_relation_predicate
    refine AxiomDecoder.indexed SyntaxDecode.context ?_
    intro free
    refine AxiomDecoder.indexed (SyntaxDecode.term [] free) ?_
    intro relation
    exact AxiomDecoder.singleton _

def decode_relation_domain_operator : AxiomDecoder IntrinsicAxiomCertificate.presentation_relation_domain_operator :=
  AxiomDecoder.insert domain_definition_axiom decode_relation_domain

def decode_relation_range : AxiomDecoder IntrinsicAxiomCertificate.presentation_relation_range :=
  by
    refine AxiomDecoder.union ?_ decode_relation_domain_operator
    refine AxiomDecoder.indexed SyntaxDecode.context ?_
    intro free
    refine AxiomDecoder.indexed (SyntaxDecode.term [] free) ?_
    intro relation
    exact AxiomDecoder.singleton _

def decode_relation_range_operator : AxiomDecoder IntrinsicAxiomCertificate.presentation_relation_range_operator :=
  AxiomDecoder.insert range_definition_axiom decode_relation_range

def decode_subset : AxiomDecoder IntrinsicAxiomCertificate.presentation_subset :=
  AxiomDecoder.insert subset_definition_axiom decode_extensionality

def decode_power_set : AxiomDecoder IntrinsicAxiomCertificate.presentation_power_set :=
  AxiomDecoder.insert power_set_axiom decode_subset

def decode_power_set_operator : AxiomDecoder IntrinsicAxiomCertificate.presentation_power_set_operator :=
  AxiomDecoder.insert power_set_definition_axiom decode_power_set

def decode_cartesian_product_base : AxiomDecoder IntrinsicAxiomCertificate.presentation_cartesian_product_base :=
  AxiomDecoder.union decode_ordered_pair_operator
      (AxiomDecoder.union decode_power_set_operator
        decode_binary_union_operator)

def decode_cartesian_product : AxiomDecoder IntrinsicAxiomCertificate.presentation_cartesian_product := by
  refine AxiomDecoder.union ?_ decode_cartesian_product_base
  refine AxiomDecoder.indexed SyntaxDecode.context ?_
  intro free
  refine AxiomDecoder.indexed (SyntaxDecode.term [] free) ?_
  intro left
  refine AxiomDecoder.indexed (SyntaxDecode.term [] free) ?_
  intro right
  exact AxiomDecoder.singleton _

def decode_cartesian_product_operator : AxiomDecoder IntrinsicAxiomCertificate.presentation_cartesian_product_operator :=
  AxiomDecoder.insert cartesian_product_definition_axiom decode_cartesian_product

def decode_ordered_pair_reverse_operator : AxiomDecoder IntrinsicAxiomCertificate.presentation_ordered_pair_reverse_operator :=
  AxiomDecoder.insert ordered_pair_reverse_definition_axiom
      decode_right_projection_operator

def decode_relation_plane : AxiomDecoder IntrinsicAxiomCertificate.presentation_relation_plane :=
  AxiomDecoder.union decode_relation_range_operator
      (AxiomDecoder.union decode_cartesian_product_operator
        decode_ordered_pair_reverse_operator)

def decode_relation_converse : AxiomDecoder IntrinsicAxiomCertificate.presentation_relation_converse := by
  refine AxiomDecoder.union ?_ decode_relation_plane
  refine AxiomDecoder.indexed SyntaxDecode.context ?_
  intro free
  refine AxiomDecoder.indexed (SyntaxDecode.term [] free) ?_
  intro relation
  exact AxiomDecoder.singleton _

def decode_relation_converse_operator : AxiomDecoder IntrinsicAxiomCertificate.presentation_relation_converse_operator :=
  AxiomDecoder.insert relation_converse_definition_axiom decode_relation_converse

def decode_relation_composition : AxiomDecoder IntrinsicAxiomCertificate.presentation_relation_composition := by
  refine AxiomDecoder.union ?_ decode_relation_converse_operator
  refine AxiomDecoder.indexed SyntaxDecode.context ?_
  intro free
  refine AxiomDecoder.indexed (SyntaxDecode.term [] free) ?_
  intro first
  refine AxiomDecoder.indexed (SyntaxDecode.term [] free) ?_
  intro second
  exact AxiomDecoder.singleton _

def decode_relation_composition_operator : AxiomDecoder IntrinsicAxiomCertificate.presentation_relation_composition_operator :=
  AxiomDecoder.insert relation_composition_definition_axiom
      decode_relation_composition

def decode_equivalence_relation : AxiomDecoder IntrinsicAxiomCertificate.presentation_equivalence_relation :=
  AxiomDecoder.insert is_equivalence_relation_definition_axiom
      decode_relation_composition_operator

def decode_function_predicate : AxiomDecoder IntrinsicAxiomCertificate.presentation_function_predicate :=
  AxiomDecoder.insert is_function_definition_axiom decode_equivalence_relation

def decode_mapping_predicate : AxiomDecoder IntrinsicAxiomCertificate.presentation_mapping_predicate :=
  AxiomDecoder.insert is_mapping_definition_axiom decode_function_predicate

def decode_function_application : AxiomDecoder IntrinsicAxiomCertificate.presentation_function_application :=
  AxiomDecoder.insert function_application_definition_axiom decode_mapping_predicate

def decode_injective_predicate : AxiomDecoder IntrinsicAxiomCertificate.presentation_injective_predicate :=
  AxiomDecoder.insert is_injective_definition_axiom decode_function_application

def decode_surjective_predicate : AxiomDecoder IntrinsicAxiomCertificate.presentation_surjective_predicate :=
  AxiomDecoder.insert is_surjective_definition_axiom decode_injective_predicate

def decode_bijection_predicate : AxiomDecoder IntrinsicAxiomCertificate.presentation_bijection_predicate :=
  AxiomDecoder.insert is_bijection_definition_axiom decode_surjective_predicate

def decode_identity : AxiomDecoder IntrinsicAxiomCertificate.presentation_identity := by
  refine AxiomDecoder.union ?_ decode_bijection_predicate
  refine AxiomDecoder.indexed SyntaxDecode.context ?_
  intro free
  refine AxiomDecoder.indexed (SyntaxDecode.term [] free) ?_
  intro source
  exact AxiomDecoder.singleton _

def decode_identity_operator : AxiomDecoder IntrinsicAxiomCertificate.presentation_identity_operator :=
  AxiomDecoder.insert identity_definition_axiom decode_identity

def decode_mapping_collection : AxiomDecoder IntrinsicAxiomCertificate.presentation_mapping_collection := by
  refine AxiomDecoder.union ?_ decode_identity_operator
  refine AxiomDecoder.indexed SyntaxDecode.context ?_
  intro free
  refine AxiomDecoder.indexed (SyntaxDecode.term [] free) ?_
  intro source
  refine AxiomDecoder.indexed (SyntaxDecode.term [] free) ?_
  intro target
  exact AxiomDecoder.singleton _

def decode_mapping_collection_operator : AxiomDecoder IntrinsicAxiomCertificate.presentation_mapping_collection_operator :=
  AxiomDecoder.insert mapping_collection_definition_axiom decode_mapping_collection

def decode_transitive_set : AxiomDecoder IntrinsicAxiomCertificate.presentation_transitive_set :=
  AxiomDecoder.insert is_transitive_set_definition_axiom
      decode_mapping_collection_operator

def decode_membership_relation : AxiomDecoder IntrinsicAxiomCertificate.presentation_membership_relation :=
  AxiomDecoder.insert membership_relation_predicate.separation_axiom
      decode_transitive_set

def decode_membership_relation_operator : AxiomDecoder IntrinsicAxiomCertificate.presentation_membership_relation_operator :=
  AxiomDecoder.insert membership_relation_definition_axiom
      decode_membership_relation

def decode_linear_order : AxiomDecoder IntrinsicAxiomCertificate.presentation_linear_order :=
  AxiomDecoder.insert is_linear_order_definition_axiom
      decode_membership_relation_operator

def decode_order_isomorphism : AxiomDecoder IntrinsicAxiomCertificate.presentation_order_isomorphism :=
  AxiomDecoder.insert is_order_isomorphism_definition_axiom decode_linear_order

def decode_order_isomorphic : AxiomDecoder IntrinsicAxiomCertificate.presentation_order_isomorphic :=
  AxiomDecoder.insert is_order_isomorphic_definition_axiom decode_order_isomorphism

def decode_order_embedding : AxiomDecoder IntrinsicAxiomCertificate.presentation_order_embedding :=
  AxiomDecoder.insert is_order_embedding_definition_axiom decode_order_isomorphic

def decode_order_embeddable : AxiomDecoder IntrinsicAxiomCertificate.presentation_order_embeddable :=
  AxiomDecoder.insert is_order_embeddable_definition_axiom decode_order_embedding

def decode_natural_discrete_linear_order : AxiomDecoder IntrinsicAxiomCertificate.presentation_natural_discrete_linear_order :=
  AxiomDecoder.insert is_natural_discrete_linear_order_definition_axiom
      decode_order_embeddable

def decode_well_order : AxiomDecoder IntrinsicAxiomCertificate.presentation_well_order :=
  AxiomDecoder.insert well_order_definition_axiom
      decode_natural_discrete_linear_order

def decode_finite_ordinal : AxiomDecoder IntrinsicAxiomCertificate.presentation_finite_ordinal :=
  decode_well_order

def decode_relation_image_separation : AxiomDecoder IntrinsicAxiomCertificate.presentation_relation_image_separation :=
  AxiomDecoder.insert relation_image_separation_axiom decode_finite_ordinal

def decode_image_operator : AxiomDecoder IntrinsicAxiomCertificate.presentation_image_operator :=
  AxiomDecoder.insert image_definition_axiom decode_relation_image_separation

def decode_restriction_operator : AxiomDecoder IntrinsicAxiomCertificate.presentation_restriction_operator :=
  AxiomDecoder.insert restriction_definition_axiom decode_image_operator

def decode_minimum_linear_order : AxiomDecoder IntrinsicAxiomCertificate.presentation_minimum_linear_order :=
  AxiomDecoder.insert minimum_linear_order_definition_axiom decode_restriction_operator

def decode_minimum_natural_order : AxiomDecoder IntrinsicAxiomCertificate.presentation_minimum_natural_order :=
  AxiomDecoder.insert minimum_natural_order_definition_axiom decode_minimum_linear_order

def decode_order_operator : AxiomDecoder IntrinsicAxiomCertificate.presentation_order_operator :=
  AxiomDecoder.insert maximum_natural_order_definition_axiom decode_minimum_natural_order

def decode_minimum_difference : AxiomDecoder IntrinsicAxiomCertificate.presentation_minimum_difference :=
  AxiomDecoder.insert minimum_difference_definition_axiom decode_order_operator

def decode_index_order_separation : AxiomDecoder IntrinsicAxiomCertificate.presentation_index_order_separation := by
  refine AxiomDecoder.union ?_ decode_minimum_difference
  refine AxiomDecoder.indexed SyntaxDecode.context ?_
  intro free
  refine AxiomDecoder.indexed (SyntaxDecode.term [] free) ?_
  intro sourceRelation
  refine AxiomDecoder.indexed (SyntaxDecode.term [] free) ?_
  intro sourceCarrier
  refine AxiomDecoder.indexed (SyntaxDecode.term [] free) ?_
  intro targetRelation
  refine AxiomDecoder.indexed (SyntaxDecode.term [] free) ?_
  intro targetCarrier
  exact AxiomDecoder.singleton _

def decode_index_order : AxiomDecoder IntrinsicAxiomCertificate.presentation_index_order :=
  AxiomDecoder.insert index_order_definition_axiom decode_index_order_separation

def decode_power_set_bijection_separation : AxiomDecoder IntrinsicAxiomCertificate.presentation_power_set_bijection_separation := by
  refine AxiomDecoder.union ?_ decode_index_order
  refine AxiomDecoder.indexed SyntaxDecode.context ?_
  intro free
  refine AxiomDecoder.indexed (SyntaxDecode.term [] free) ?_
  intro natural
  exact AxiomDecoder.singleton _

def decode_power_set_bijection : AxiomDecoder IntrinsicAxiomCertificate.presentation_power_set_bijection :=
  AxiomDecoder.insert power_set_bijection_definition_axiom
      decode_power_set_bijection_separation

def decode_symmetric_difference_separation : AxiomDecoder IntrinsicAxiomCertificate.presentation_symmetric_difference_separation := by
  refine AxiomDecoder.union ?_ decode_power_set_bijection
  refine AxiomDecoder.indexed SyntaxDecode.context ?_
  intro free
  refine AxiomDecoder.indexed (SyntaxDecode.term [] free) ?_
  intro left
  refine AxiomDecoder.indexed (SyntaxDecode.term [] free) ?_
  intro right
  exact AxiomDecoder.singleton _

def decode_symmetric_difference : AxiomDecoder IntrinsicAxiomCertificate.presentation_symmetric_difference :=
  AxiomDecoder.insert symmetric_difference_definition_axiom
      decode_symmetric_difference_separation

def decode_finite_predicate : AxiomDecoder IntrinsicAxiomCertificate.presentation_finite_predicate :=
  AxiomDecoder.insert is_finite_definition_axiom decode_symmetric_difference

def decode_equinumerous_predicate : AxiomDecoder IntrinsicAxiomCertificate.presentation_equinumerous_predicate :=
  AxiomDecoder.insert is_equinumerous_definition_axiom decode_finite_predicate

def decode_cardinality_leq_predicate : AxiomDecoder IntrinsicAxiomCertificate.presentation_cardinality_leq_predicate :=
  AxiomDecoder.insert cardinality_leq_definition_axiom
      decode_equinumerous_predicate

def decode_cardinality_strict_less_predicate : AxiomDecoder IntrinsicAxiomCertificate.presentation_cardinality_strict_less_predicate :=
  AxiomDecoder.insert cardinality_strict_less_definition_axiom
      decode_cardinality_leq_predicate

def decode_dedekind_finite_predicate : AxiomDecoder IntrinsicAxiomCertificate.presentation_dedekind_finite_predicate :=
  AxiomDecoder.insert is_dedekind_finite_definition_axiom
      decode_cardinality_strict_less_predicate

def decode_basic_finite : AxiomDecoder IntrinsicAxiomCertificate.presentation_basic_finite :=
  decode_dedekind_finite_predicate

def decode_infinity_axiom : AxiomDecoder IntrinsicAxiomCertificate.presentation_infinity_axiom :=
  AxiomDecoder.insert infinity_axiom decode_basic_finite

def decode_inductive_set : AxiomDecoder IntrinsicAxiomCertificate.presentation_inductive_set :=
  AxiomDecoder.insert is_inductive_set_definition_axiom decode_infinity_axiom

def decode_inductive_core_separation : AxiomDecoder IntrinsicAxiomCertificate.presentation_inductive_core_separation := by
  refine AxiomDecoder.union ?_ decode_inductive_set
  refine AxiomDecoder.indexed SyntaxDecode.context ?_
  intro free
  refine AxiomDecoder.indexed (SyntaxDecode.term [] free) ?_
  intro source
  exact AxiomDecoder.singleton _

def decode_inductive_core : AxiomDecoder IntrinsicAxiomCertificate.presentation_inductive_core :=
  AxiomDecoder.insert inductive_core_definition_axiom
      decode_inductive_core_separation

def decode_infinity : AxiomDecoder IntrinsicAxiomCertificate.presentation_infinity :=
  AxiomDecoder.insert omega_definition_axiom decode_inductive_core

def decode_unbounded_subset : AxiomDecoder IntrinsicAxiomCertificate.presentation_unbounded_subset :=
  AxiomDecoder.insert unbounded_subset_definition_axiom decode_infinity

def decode_bounded_subset : AxiomDecoder IntrinsicAxiomCertificate.presentation_bounded_subset :=
  AxiomDecoder.insert bounded_subset_definition_axiom decode_unbounded_subset

def decode_natural_order_type : AxiomDecoder IntrinsicAxiomCertificate.presentation_natural_order_type :=
  AxiomDecoder.insert natural_order_type_definition_axiom decode_bounded_subset

def decode_natural_subset_type : AxiomDecoder IntrinsicAxiomCertificate.presentation_natural_subset_type :=
  AxiomDecoder.insert natural_subset_type_definition_axiom decode_natural_order_type

def decode_natural_set : AxiomDecoder IntrinsicAxiomCertificate.presentation_natural_set :=
  decode_natural_subset_type

def decode_natural_addition : AxiomDecoder IntrinsicAxiomCertificate.presentation_natural_addition :=
  AxiomDecoder.insert natural_addition_definition_axiom decode_natural_set

def decode_natural_multiplication : AxiomDecoder IntrinsicAxiomCertificate.presentation_natural_multiplication :=
  AxiomDecoder.insert natural_multiplication_definition_axiom
      decode_natural_addition

def decode_natural_exponentiation : AxiomDecoder IntrinsicAxiomCertificate.presentation_natural_exponentiation :=
  AxiomDecoder.insert natural_exponentiation_definition_axiom
      decode_natural_multiplication

def decode_godel_pairing_core : AxiomDecoder IntrinsicAxiomCertificate.presentation_godel_pairing_core :=
  AxiomDecoder.insert godel_pairing_definition_axiom
      decode_natural_exponentiation

def decode_natural_exponentiation_bound : AxiomDecoder IntrinsicAxiomCertificate.presentation_natural_exponentiation_bound :=
  AxiomDecoder.insert natural_exponentiation_index_bound_axiom
      (AxiomDecoder.insert natural_exponent_product_index_bound_axiom
        decode_godel_pairing_core)

def decode_natural_addition_bound : AxiomDecoder IntrinsicAxiomCertificate.presentation_natural_addition_bound :=
  AxiomDecoder.insert natural_addition_upper_bound_axiom
      (AxiomDecoder.insert natural_positive_left_addition_strict_bound_axiom
        (AxiomDecoder.insert natural_le_lt_transitivity_axiom
          (AxiomDecoder.insert natural_godel_pairing_coordinate_bound_axiom
            decode_natural_exponentiation_bound)))

def decode_formal_language_encoding : AxiomDecoder IntrinsicAxiomCertificate.presentation_formal_language_encoding :=
  AxiomDecoder.insert structural_syntax_definition_axiom
      (AxiomDecoder.union decode_successor_operator decode_natural_addition_bound)

def decode_membership_irreflexive : AxiomDecoder IntrinsicAxiomCertificate.presentation_membership_irreflexive :=
  AxiomDecoder.singleton membership_irreflexive_axiom

def decode_empty_set : AxiomDecoder IntrinsicAxiomCertificate.presentation_empty_set :=
  AxiomDecoder.insert (empty_predicate (free := [])).separation_axiom
      decode_extensionality

def decode_empty_set_symbol : AxiomDecoder IntrinsicAxiomCertificate.presentation_empty_set_symbol :=
  AxiomDecoder.insert empty_set_definition_axiom decode_empty_set

def decode_infinite_predicate : AxiomDecoder IntrinsicAxiomCertificate.presentation_infinite_predicate :=
  AxiomDecoder.insert is_infinite_definition_axiom decode_natural_exponentiation

def decode_countable_predicate : AxiomDecoder IntrinsicAxiomCertificate.presentation_countable_predicate :=
  AxiomDecoder.insert is_countable_definition_axiom decode_infinite_predicate

def decode_uncountable_predicate : AxiomDecoder IntrinsicAxiomCertificate.presentation_uncountable_predicate :=
  AxiomDecoder.insert is_uncountable_definition_axiom decode_countable_predicate

def decode_countably_infinite_predicate : AxiomDecoder IntrinsicAxiomCertificate.presentation_countably_infinite_predicate :=
  AxiomDecoder.insert is_countably_infinite_definition_axiom
      decode_uncountable_predicate

def decode_cardinality_classification : AxiomDecoder IntrinsicAxiomCertificate.presentation_cardinality_classification :=
  decode_countably_infinite_predicate

def decode_finite_sequence_space : AxiomDecoder IntrinsicAxiomCertificate.presentation_finite_sequence_space :=
  AxiomDecoder.insert finite_sequence_space_definition_axiom
      decode_cardinality_classification

def decode_recursive_sequence_space : AxiomDecoder IntrinsicAxiomCertificate.presentation_recursive_sequence_space :=
  AxiomDecoder.insert recursive_sequence_space_definition_axiom
      decode_finite_sequence_space

def decode_omega_recursive_sequence : AxiomDecoder IntrinsicAxiomCertificate.presentation_omega_recursive_sequence :=
  AxiomDecoder.insert omega_recursive_sequence_definition_axiom
      decode_recursive_sequence_space

def decode_natural_difference : AxiomDecoder IntrinsicAxiomCertificate.presentation_natural_difference :=
  AxiomDecoder.insert natural_difference_definition_axiom
      decode_omega_recursive_sequence

def decode_omega_pair_order : AxiomDecoder IntrinsicAxiomCertificate.presentation_omega_pair_order :=
  AxiomDecoder.insert omega_pair_less_definition_axiom decode_natural_difference

def decode_godel_pairing : AxiomDecoder IntrinsicAxiomCertificate.presentation_godel_pairing :=
  AxiomDecoder.insert godel_pairing_definition_axiom decode_omega_pair_order

def decode_natural_arithmetic : AxiomDecoder IntrinsicAxiomCertificate.presentation_natural_arithmetic :=
  decode_godel_pairing

def decode_transitive_closure_operator : AxiomDecoder IntrinsicAxiomCertificate.presentation_transitive_closure_operator :=
  AxiomDecoder.insert transitive_closure_definition_axiom decode_natural_arithmetic

def decode_finite_hierarchy_operator : AxiomDecoder IntrinsicAxiomCertificate.presentation_finite_hierarchy_operator :=
  AxiomDecoder.insert finite_hierarchy_definition_axiom decode_transitive_closure_operator

def decode_finite_universe_operator : AxiomDecoder IntrinsicAxiomCertificate.presentation_finite_universe_operator :=
  AxiomDecoder.insert finite_universe_definition_axiom decode_finite_hierarchy_operator

def decode_hereditarily_finite_predicate : AxiomDecoder IntrinsicAxiomCertificate.presentation_hereditarily_finite_predicate :=
  AxiomDecoder.insert hereditarily_finite_definition_axiom decode_finite_universe_operator

def decode_finite_subset_collection_separation : AxiomDecoder IntrinsicAxiomCertificate.presentation_finite_subset_collection_separation :=
  AxiomDecoder.insert finite_subset_collection_separation_axiom
      decode_hereditarily_finite_predicate

def decode_finite_subset_collection_operator : AxiomDecoder IntrinsicAxiomCertificate.presentation_finite_subset_collection_operator :=
  AxiomDecoder.insert finite_subset_collection_definition_axiom
      decode_finite_subset_collection_separation

def decode_hereditarily_finite : AxiomDecoder IntrinsicAxiomCertificate.presentation_hereditarily_finite :=
  decode_finite_subset_collection_operator

def decode_finite_sequence_concatenation : AxiomDecoder IntrinsicAxiomCertificate.presentation_finite_sequence_concatenation :=
  AxiomDecoder.insert finite_sequence_concatenation_definition_axiom decode_hereditarily_finite

def decode_nonempty_finite_sequence_space_separation : AxiomDecoder IntrinsicAxiomCertificate.presentation_nonempty_finite_sequence_space_separation :=
  AxiomDecoder.insert nonempty_finite_sequence_space_separation_axiom
      decode_finite_sequence_concatenation

def decode_nonempty_finite_sequence_space : AxiomDecoder IntrinsicAxiomCertificate.presentation_nonempty_finite_sequence_space :=
  AxiomDecoder.insert nonempty_finite_sequence_space_definition_axiom
      decode_nonempty_finite_sequence_space_separation

def decode_finite_sequence_flatten : AxiomDecoder IntrinsicAxiomCertificate.presentation_finite_sequence_flatten :=
  AxiomDecoder.insert finite_sequence_flatten_definition_axiom
      decode_nonempty_finite_sequence_space

def decode_finite_sequence_support : AxiomDecoder IntrinsicAxiomCertificate.presentation_finite_sequence_support :=
  AxiomDecoder.union decode_membership_irreflexive <|
      AxiomDecoder.union decode_empty_set_symbol <|
        AxiomDecoder.union decode_successor_operator <|
          AxiomDecoder.union decode_binary_union_operator <|
            AxiomDecoder.union decode_ordered_pair_operator <|
              AxiomDecoder.union decode_function_application <|
                AxiomDecoder.union decode_finite_sequence_flatten
                  decode_finite_sequence_space

def decode_intrinsic_arithmetic_evaluation : AxiomDecoder IntrinsicAxiomCertificate.presentation_intrinsic_arithmetic_evaluation :=
  AxiomDecoder.union decode_formal_language_encoding
      decode_finite_sequence_support

def decode_expression_encoding : AxiomDecoder IntrinsicAxiomCertificate.presentation_expression_encoding :=
  AxiomDecoder.union decode_membership_irreflexive
      (AxiomDecoder.union
        (AxiomDecoder.insert free_variable_occurs_definition_axiom
          (AxiomDecoder.insert syntax_transform_definition_axiom
            decode_formal_language_encoding))
        decode_empty_set_symbol)

def decode_propositional_axiom_schema : AxiomDecoder IntrinsicAxiomCertificate.presentation_propositional_axiom_schema :=
  AxiomDecoder.insert propositional_axiom_schema_definition_axiom
      decode_expression_encoding

def decode_quantifier_axiom_schema : AxiomDecoder IntrinsicAxiomCertificate.presentation_quantifier_axiom_schema :=
  AxiomDecoder.insert quantifier_axiom_schema_definition_axiom
      decode_propositional_axiom_schema

def decode_equality_axiom_schema : AxiomDecoder IntrinsicAxiomCertificate.presentation_equality_axiom_schema :=
  AxiomDecoder.insert equality_axiom_schema_definition_axiom
      decode_quantifier_axiom_schema

def decode_logical_axiom_code : AxiomDecoder IntrinsicAxiomCertificate.presentation_logical_axiom_code :=
  AxiomDecoder.insert logical_axiom_code_definition_axiom
      decode_equality_axiom_schema

def decode_logical_rule_encoding : AxiomDecoder IntrinsicAxiomCertificate.presentation_logical_rule_encoding :=
  AxiomDecoder.insert modus_ponens_definition_axiom
      decode_logical_axiom_code

def decode_related_symbol_semantics : AxiomDecoder IntrinsicAxiomCertificate.presentation_related_symbol_semantics :=
  AxiomDecoder.insert related_nonlogical_symbol_set_definition_axiom
      decode_logical_rule_encoding

def decode_related_syntax_semantics : AxiomDecoder IntrinsicAxiomCertificate.presentation_related_syntax_semantics :=
  AxiomDecoder.insert related_syntax_definition_axiom decode_related_symbol_semantics

def decode_structure_semantics : AxiomDecoder IntrinsicAxiomCertificate.presentation_structure_semantics :=
  AxiomDecoder.insert structure_definition_axiom decode_related_syntax_semantics

def decode_term_value_semantics : AxiomDecoder IntrinsicAxiomCertificate.presentation_term_value_semantics :=
  AxiomDecoder.insert (term_value_definition_axiom ∧ₘ term_list_value_definition_axiom)
      decode_structure_semantics

def decode_semantic_interpretation : AxiomDecoder IntrinsicAxiomCertificate.presentation_semantic_interpretation :=
  decode_term_value_semantics

def decode_intrinsic_syntax_carrier : AxiomDecoder IntrinsicAxiomCertificate.presentation_intrinsic_syntax_carrier :=
  AxiomDecoder.union (AxiomDecoder.union decode_subset decode_empty_set_symbol)
      decode_semantic_interpretation

def decode_intrinsic_proof_row : AxiomDecoder IntrinsicAxiomCertificate.presentation_intrinsic_proof_row :=
  AxiomDecoder.union decode_intrinsic_syntax_carrier
      decode_finite_sequence_support

def decode_intrinsic_proof : AxiomDecoder IntrinsicAxiomCertificate.presentation_intrinsic_proof :=
  AxiomDecoder.union decode_intrinsic_arithmetic_evaluation
      decode_intrinsic_proof_row

end IntrinsicAxiomDecode

def intrinsic_proof_axiom_decode : AxiomDecoder intrinsic_proof_axiom_presentation :=
  IntrinsicAxiomDecode.decode_intrinsic_proof
end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT
