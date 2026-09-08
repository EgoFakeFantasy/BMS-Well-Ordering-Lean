import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicAxiomDecode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.AxiomEncode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SyntaxEncode

/-! # 全部支撑公理呈现的编码与往返定理 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT
open Nonlogical.BasicSetTheory
set_option autoImplicit false
namespace IntrinsicAxiomEncode

def codec_extensionality : AxiomCodec IntrinsicAxiomDecode.decode_extensionality :=
  AxiomCodec.singleton extensionality_axiom

def codec_pairing : AxiomCodec IntrinsicAxiomDecode.decode_pairing :=
  AxiomCodec.insert pairing_axiom codec_extensionality

def codec_pairing_operator : AxiomCodec IntrinsicAxiomDecode.decode_pairing_operator :=
  AxiomCodec.insert pair_definition_axiom codec_pairing

def codec_union : AxiomCodec IntrinsicAxiomDecode.decode_union :=
  AxiomCodec.insert union_axiom codec_extensionality

def codec_union_operator : AxiomCodec IntrinsicAxiomDecode.decode_union_operator :=
  AxiomCodec.insert union_definition_axiom codec_union

def codec_binary_union_base : AxiomCodec IntrinsicAxiomDecode.decode_binary_union_base :=
  AxiomCodec.union codec_pairing_operator codec_union_operator

def codec_binary_union_operator : AxiomCodec IntrinsicAxiomDecode.decode_binary_union_operator :=
  AxiomCodec.insert
      binary_union_definition_axiom
      codec_binary_union_base

def codec_successor_base : AxiomCodec IntrinsicAxiomDecode.decode_successor_base :=
  codec_binary_union_operator

def codec_successor_operator : AxiomCodec IntrinsicAxiomDecode.decode_successor_operator :=
  AxiomCodec.insert successor_definition_axiom codec_successor_base

def codec_singleton_operator : AxiomCodec IntrinsicAxiomDecode.decode_singleton_operator :=
  AxiomCodec.insert singleton_definition_axiom codec_pairing_operator

def codec_ordered_pair_operator : AxiomCodec IntrinsicAxiomDecode.decode_ordered_pair_operator :=
  AxiomCodec.insert ordered_pair_definition_axiom codec_singleton_operator

def codec_relation_function : AxiomCodec IntrinsicAxiomDecode.decode_relation_function :=
  AxiomCodec.insert is_ordered_pair_definition_axiom codec_ordered_pair_operator

def codec_left_projection_operator : AxiomCodec IntrinsicAxiomDecode.decode_left_projection_operator :=
  AxiomCodec.insert left_projection_definition_axiom codec_relation_function

def codec_right_projection_operator : AxiomCodec IntrinsicAxiomDecode.decode_right_projection_operator :=
  AxiomCodec.insert right_projection_definition_axiom codec_left_projection_operator

def codec_relation_base : AxiomCodec IntrinsicAxiomDecode.decode_relation_base :=
  AxiomCodec.union codec_right_projection_operator codec_union_operator

def codec_relation_predicate : AxiomCodec IntrinsicAxiomDecode.decode_relation_predicate :=
  AxiomCodec.insert is_relation_definition_axiom codec_relation_base

def codec_relation_domain : AxiomCodec IntrinsicAxiomDecode.decode_relation_domain :=
  by
    refine AxiomCodec.union ?_ codec_relation_predicate
    refine AxiomCodec.indexed SyntaxEncode.context SyntaxEncode.context_roundtrip ?_
    intro free
    refine AxiomCodec.indexed SyntaxEncode.term SyntaxEncode.term_roundtrip ?_
    intro relation
    exact AxiomCodec.singleton _

def codec_relation_domain_operator : AxiomCodec IntrinsicAxiomDecode.decode_relation_domain_operator :=
  AxiomCodec.insert domain_definition_axiom codec_relation_domain

def codec_relation_range : AxiomCodec IntrinsicAxiomDecode.decode_relation_range :=
  by
    refine AxiomCodec.union ?_ codec_relation_domain_operator
    refine AxiomCodec.indexed SyntaxEncode.context SyntaxEncode.context_roundtrip ?_
    intro free
    refine AxiomCodec.indexed SyntaxEncode.term SyntaxEncode.term_roundtrip ?_
    intro relation
    exact AxiomCodec.singleton _

def codec_relation_range_operator : AxiomCodec IntrinsicAxiomDecode.decode_relation_range_operator :=
  AxiomCodec.insert range_definition_axiom codec_relation_range

def codec_subset : AxiomCodec IntrinsicAxiomDecode.decode_subset :=
  AxiomCodec.insert subset_definition_axiom codec_extensionality

def codec_power_set : AxiomCodec IntrinsicAxiomDecode.decode_power_set :=
  AxiomCodec.insert power_set_axiom codec_subset

def codec_power_set_operator : AxiomCodec IntrinsicAxiomDecode.decode_power_set_operator :=
  AxiomCodec.insert power_set_definition_axiom codec_power_set

def codec_cartesian_product_base : AxiomCodec IntrinsicAxiomDecode.decode_cartesian_product_base :=
  AxiomCodec.union codec_ordered_pair_operator
      (AxiomCodec.union codec_power_set_operator
        codec_binary_union_operator)

def codec_cartesian_product : AxiomCodec IntrinsicAxiomDecode.decode_cartesian_product := by
  refine AxiomCodec.union ?_ codec_cartesian_product_base
  refine AxiomCodec.indexed SyntaxEncode.context SyntaxEncode.context_roundtrip ?_
  intro free
  refine AxiomCodec.indexed SyntaxEncode.term SyntaxEncode.term_roundtrip ?_
  intro left
  refine AxiomCodec.indexed SyntaxEncode.term SyntaxEncode.term_roundtrip ?_
  intro right
  exact AxiomCodec.singleton _

def codec_cartesian_product_operator : AxiomCodec IntrinsicAxiomDecode.decode_cartesian_product_operator :=
  AxiomCodec.insert cartesian_product_definition_axiom codec_cartesian_product

def codec_ordered_pair_reverse_operator : AxiomCodec IntrinsicAxiomDecode.decode_ordered_pair_reverse_operator :=
  AxiomCodec.insert ordered_pair_reverse_definition_axiom
      codec_right_projection_operator

def codec_relation_plane : AxiomCodec IntrinsicAxiomDecode.decode_relation_plane :=
  AxiomCodec.union codec_relation_range_operator
      (AxiomCodec.union codec_cartesian_product_operator
        codec_ordered_pair_reverse_operator)

def codec_relation_converse : AxiomCodec IntrinsicAxiomDecode.decode_relation_converse := by
  refine AxiomCodec.union ?_ codec_relation_plane
  refine AxiomCodec.indexed SyntaxEncode.context SyntaxEncode.context_roundtrip ?_
  intro free
  refine AxiomCodec.indexed SyntaxEncode.term SyntaxEncode.term_roundtrip ?_
  intro relation
  exact AxiomCodec.singleton _

def codec_relation_converse_operator : AxiomCodec IntrinsicAxiomDecode.decode_relation_converse_operator :=
  AxiomCodec.insert relation_converse_definition_axiom codec_relation_converse

def codec_relation_composition : AxiomCodec IntrinsicAxiomDecode.decode_relation_composition := by
  refine AxiomCodec.union ?_ codec_relation_converse_operator
  refine AxiomCodec.indexed SyntaxEncode.context SyntaxEncode.context_roundtrip ?_
  intro free
  refine AxiomCodec.indexed SyntaxEncode.term SyntaxEncode.term_roundtrip ?_
  intro first
  refine AxiomCodec.indexed SyntaxEncode.term SyntaxEncode.term_roundtrip ?_
  intro second
  exact AxiomCodec.singleton _

def codec_relation_composition_operator : AxiomCodec IntrinsicAxiomDecode.decode_relation_composition_operator :=
  AxiomCodec.insert relation_composition_definition_axiom
      codec_relation_composition

def codec_equivalence_relation : AxiomCodec IntrinsicAxiomDecode.decode_equivalence_relation :=
  AxiomCodec.insert is_equivalence_relation_definition_axiom
      codec_relation_composition_operator

def codec_function_predicate : AxiomCodec IntrinsicAxiomDecode.decode_function_predicate :=
  AxiomCodec.insert is_function_definition_axiom codec_equivalence_relation

def codec_mapping_predicate : AxiomCodec IntrinsicAxiomDecode.decode_mapping_predicate :=
  AxiomCodec.insert is_mapping_definition_axiom codec_function_predicate

def codec_function_application : AxiomCodec IntrinsicAxiomDecode.decode_function_application :=
  AxiomCodec.insert function_application_definition_axiom codec_mapping_predicate

def codec_injective_predicate : AxiomCodec IntrinsicAxiomDecode.decode_injective_predicate :=
  AxiomCodec.insert is_injective_definition_axiom codec_function_application

def codec_surjective_predicate : AxiomCodec IntrinsicAxiomDecode.decode_surjective_predicate :=
  AxiomCodec.insert is_surjective_definition_axiom codec_injective_predicate

def codec_bijection_predicate : AxiomCodec IntrinsicAxiomDecode.decode_bijection_predicate :=
  AxiomCodec.insert is_bijection_definition_axiom codec_surjective_predicate

def codec_identity : AxiomCodec IntrinsicAxiomDecode.decode_identity := by
  refine AxiomCodec.union ?_ codec_bijection_predicate
  refine AxiomCodec.indexed SyntaxEncode.context SyntaxEncode.context_roundtrip ?_
  intro free
  refine AxiomCodec.indexed SyntaxEncode.term SyntaxEncode.term_roundtrip ?_
  intro source
  exact AxiomCodec.singleton _

def codec_identity_operator : AxiomCodec IntrinsicAxiomDecode.decode_identity_operator :=
  AxiomCodec.insert identity_definition_axiom codec_identity

def codec_mapping_collection : AxiomCodec IntrinsicAxiomDecode.decode_mapping_collection := by
  refine AxiomCodec.union ?_ codec_identity_operator
  refine AxiomCodec.indexed SyntaxEncode.context SyntaxEncode.context_roundtrip ?_
  intro free
  refine AxiomCodec.indexed SyntaxEncode.term SyntaxEncode.term_roundtrip ?_
  intro source
  refine AxiomCodec.indexed SyntaxEncode.term SyntaxEncode.term_roundtrip ?_
  intro target
  exact AxiomCodec.singleton _

def codec_mapping_collection_operator : AxiomCodec IntrinsicAxiomDecode.decode_mapping_collection_operator :=
  AxiomCodec.insert mapping_collection_definition_axiom codec_mapping_collection

def codec_transitive_set : AxiomCodec IntrinsicAxiomDecode.decode_transitive_set :=
  AxiomCodec.insert is_transitive_set_definition_axiom
      codec_mapping_collection_operator

def codec_membership_relation : AxiomCodec IntrinsicAxiomDecode.decode_membership_relation :=
  AxiomCodec.insert membership_relation_predicate.separation_axiom
      codec_transitive_set

def codec_membership_relation_operator : AxiomCodec IntrinsicAxiomDecode.decode_membership_relation_operator :=
  AxiomCodec.insert membership_relation_definition_axiom
      codec_membership_relation

def codec_linear_order : AxiomCodec IntrinsicAxiomDecode.decode_linear_order :=
  AxiomCodec.insert is_linear_order_definition_axiom
      codec_membership_relation_operator

def codec_order_isomorphism : AxiomCodec IntrinsicAxiomDecode.decode_order_isomorphism :=
  AxiomCodec.insert is_order_isomorphism_definition_axiom codec_linear_order

def codec_order_isomorphic : AxiomCodec IntrinsicAxiomDecode.decode_order_isomorphic :=
  AxiomCodec.insert is_order_isomorphic_definition_axiom codec_order_isomorphism

def codec_order_embedding : AxiomCodec IntrinsicAxiomDecode.decode_order_embedding :=
  AxiomCodec.insert is_order_embedding_definition_axiom codec_order_isomorphic

def codec_order_embeddable : AxiomCodec IntrinsicAxiomDecode.decode_order_embeddable :=
  AxiomCodec.insert is_order_embeddable_definition_axiom codec_order_embedding

def codec_natural_discrete_linear_order : AxiomCodec IntrinsicAxiomDecode.decode_natural_discrete_linear_order :=
  AxiomCodec.insert is_natural_discrete_linear_order_definition_axiom
      codec_order_embeddable

def codec_well_order : AxiomCodec IntrinsicAxiomDecode.decode_well_order :=
  AxiomCodec.insert well_order_definition_axiom
      codec_natural_discrete_linear_order

def codec_finite_ordinal : AxiomCodec IntrinsicAxiomDecode.decode_finite_ordinal :=
  codec_well_order

def codec_relation_image_separation : AxiomCodec IntrinsicAxiomDecode.decode_relation_image_separation :=
  AxiomCodec.insert relation_image_separation_axiom codec_finite_ordinal

def codec_image_operator : AxiomCodec IntrinsicAxiomDecode.decode_image_operator :=
  AxiomCodec.insert image_definition_axiom codec_relation_image_separation

def codec_restriction_operator : AxiomCodec IntrinsicAxiomDecode.decode_restriction_operator :=
  AxiomCodec.insert restriction_definition_axiom codec_image_operator

def codec_minimum_linear_order : AxiomCodec IntrinsicAxiomDecode.decode_minimum_linear_order :=
  AxiomCodec.insert minimum_linear_order_definition_axiom codec_restriction_operator

def codec_minimum_natural_order : AxiomCodec IntrinsicAxiomDecode.decode_minimum_natural_order :=
  AxiomCodec.insert minimum_natural_order_definition_axiom codec_minimum_linear_order

def codec_order_operator : AxiomCodec IntrinsicAxiomDecode.decode_order_operator :=
  AxiomCodec.insert maximum_natural_order_definition_axiom codec_minimum_natural_order

def codec_minimum_difference : AxiomCodec IntrinsicAxiomDecode.decode_minimum_difference :=
  AxiomCodec.insert minimum_difference_definition_axiom codec_order_operator

def codec_index_order_separation : AxiomCodec IntrinsicAxiomDecode.decode_index_order_separation := by
  refine AxiomCodec.union ?_ codec_minimum_difference
  refine AxiomCodec.indexed SyntaxEncode.context SyntaxEncode.context_roundtrip ?_
  intro free
  refine AxiomCodec.indexed SyntaxEncode.term SyntaxEncode.term_roundtrip ?_
  intro sourceRelation
  refine AxiomCodec.indexed SyntaxEncode.term SyntaxEncode.term_roundtrip ?_
  intro sourceCarrier
  refine AxiomCodec.indexed SyntaxEncode.term SyntaxEncode.term_roundtrip ?_
  intro targetRelation
  refine AxiomCodec.indexed SyntaxEncode.term SyntaxEncode.term_roundtrip ?_
  intro targetCarrier
  exact AxiomCodec.singleton _

def codec_index_order : AxiomCodec IntrinsicAxiomDecode.decode_index_order :=
  AxiomCodec.insert index_order_definition_axiom codec_index_order_separation

def codec_power_set_bijection_separation : AxiomCodec IntrinsicAxiomDecode.decode_power_set_bijection_separation := by
  refine AxiomCodec.union ?_ codec_index_order
  refine AxiomCodec.indexed SyntaxEncode.context SyntaxEncode.context_roundtrip ?_
  intro free
  refine AxiomCodec.indexed SyntaxEncode.term SyntaxEncode.term_roundtrip ?_
  intro natural
  exact AxiomCodec.singleton _

def codec_power_set_bijection : AxiomCodec IntrinsicAxiomDecode.decode_power_set_bijection :=
  AxiomCodec.insert power_set_bijection_definition_axiom
      codec_power_set_bijection_separation

def codec_symmetric_difference_separation : AxiomCodec IntrinsicAxiomDecode.decode_symmetric_difference_separation := by
  refine AxiomCodec.union ?_ codec_power_set_bijection
  refine AxiomCodec.indexed SyntaxEncode.context SyntaxEncode.context_roundtrip ?_
  intro free
  refine AxiomCodec.indexed SyntaxEncode.term SyntaxEncode.term_roundtrip ?_
  intro left
  refine AxiomCodec.indexed SyntaxEncode.term SyntaxEncode.term_roundtrip ?_
  intro right
  exact AxiomCodec.singleton _

def codec_symmetric_difference : AxiomCodec IntrinsicAxiomDecode.decode_symmetric_difference :=
  AxiomCodec.insert symmetric_difference_definition_axiom
      codec_symmetric_difference_separation

def codec_finite_predicate : AxiomCodec IntrinsicAxiomDecode.decode_finite_predicate :=
  AxiomCodec.insert is_finite_definition_axiom codec_symmetric_difference

def codec_equinumerous_predicate : AxiomCodec IntrinsicAxiomDecode.decode_equinumerous_predicate :=
  AxiomCodec.insert is_equinumerous_definition_axiom codec_finite_predicate

def codec_cardinality_leq_predicate : AxiomCodec IntrinsicAxiomDecode.decode_cardinality_leq_predicate :=
  AxiomCodec.insert cardinality_leq_definition_axiom
      codec_equinumerous_predicate

def codec_cardinality_strict_less_predicate : AxiomCodec IntrinsicAxiomDecode.decode_cardinality_strict_less_predicate :=
  AxiomCodec.insert cardinality_strict_less_definition_axiom
      codec_cardinality_leq_predicate

def codec_dedekind_finite_predicate : AxiomCodec IntrinsicAxiomDecode.decode_dedekind_finite_predicate :=
  AxiomCodec.insert is_dedekind_finite_definition_axiom
      codec_cardinality_strict_less_predicate

def codec_basic_finite : AxiomCodec IntrinsicAxiomDecode.decode_basic_finite :=
  codec_dedekind_finite_predicate

def codec_infinity_axiom : AxiomCodec IntrinsicAxiomDecode.decode_infinity_axiom :=
  AxiomCodec.insert infinity_axiom codec_basic_finite

def codec_inductive_set : AxiomCodec IntrinsicAxiomDecode.decode_inductive_set :=
  AxiomCodec.insert is_inductive_set_definition_axiom codec_infinity_axiom

def codec_inductive_core_separation : AxiomCodec IntrinsicAxiomDecode.decode_inductive_core_separation := by
  refine AxiomCodec.union ?_ codec_inductive_set
  refine AxiomCodec.indexed SyntaxEncode.context SyntaxEncode.context_roundtrip ?_
  intro free
  refine AxiomCodec.indexed SyntaxEncode.term SyntaxEncode.term_roundtrip ?_
  intro source
  exact AxiomCodec.singleton _

def codec_inductive_core : AxiomCodec IntrinsicAxiomDecode.decode_inductive_core :=
  AxiomCodec.insert inductive_core_definition_axiom
      codec_inductive_core_separation

def codec_infinity : AxiomCodec IntrinsicAxiomDecode.decode_infinity :=
  AxiomCodec.insert omega_definition_axiom codec_inductive_core

def codec_unbounded_subset : AxiomCodec IntrinsicAxiomDecode.decode_unbounded_subset :=
  AxiomCodec.insert unbounded_subset_definition_axiom codec_infinity

def codec_bounded_subset : AxiomCodec IntrinsicAxiomDecode.decode_bounded_subset :=
  AxiomCodec.insert bounded_subset_definition_axiom codec_unbounded_subset

def codec_natural_order_type : AxiomCodec IntrinsicAxiomDecode.decode_natural_order_type :=
  AxiomCodec.insert natural_order_type_definition_axiom codec_bounded_subset

def codec_natural_subset_type : AxiomCodec IntrinsicAxiomDecode.decode_natural_subset_type :=
  AxiomCodec.insert natural_subset_type_definition_axiom codec_natural_order_type

def codec_natural_set : AxiomCodec IntrinsicAxiomDecode.decode_natural_set :=
  codec_natural_subset_type

def codec_natural_addition : AxiomCodec IntrinsicAxiomDecode.decode_natural_addition :=
  AxiomCodec.insert natural_addition_definition_axiom codec_natural_set

def codec_natural_multiplication : AxiomCodec IntrinsicAxiomDecode.decode_natural_multiplication :=
  AxiomCodec.insert natural_multiplication_definition_axiom
      codec_natural_addition

def codec_natural_exponentiation : AxiomCodec IntrinsicAxiomDecode.decode_natural_exponentiation :=
  AxiomCodec.insert natural_exponentiation_definition_axiom
      codec_natural_multiplication

def codec_godel_pairing_core : AxiomCodec IntrinsicAxiomDecode.decode_godel_pairing_core :=
  AxiomCodec.insert godel_pairing_definition_axiom
      codec_natural_exponentiation

def codec_natural_exponentiation_bound : AxiomCodec IntrinsicAxiomDecode.decode_natural_exponentiation_bound :=
  AxiomCodec.insert natural_exponentiation_index_bound_axiom
      (AxiomCodec.insert natural_exponent_product_index_bound_axiom
        codec_godel_pairing_core)

def codec_natural_addition_bound : AxiomCodec IntrinsicAxiomDecode.decode_natural_addition_bound :=
  AxiomCodec.insert natural_addition_upper_bound_axiom
      (AxiomCodec.insert natural_positive_left_addition_strict_bound_axiom
        (AxiomCodec.insert natural_le_lt_transitivity_axiom
          (AxiomCodec.insert natural_godel_pairing_coordinate_bound_axiom
            codec_natural_exponentiation_bound)))

def codec_formal_language_encoding : AxiomCodec IntrinsicAxiomDecode.decode_formal_language_encoding :=
  AxiomCodec.insert structural_syntax_definition_axiom
      (AxiomCodec.union codec_successor_operator codec_natural_addition_bound)

def codec_membership_irreflexive : AxiomCodec IntrinsicAxiomDecode.decode_membership_irreflexive :=
  AxiomCodec.singleton membership_irreflexive_axiom

def codec_empty_set : AxiomCodec IntrinsicAxiomDecode.decode_empty_set :=
  AxiomCodec.insert (empty_predicate (free := [])).separation_axiom
      codec_extensionality

def codec_empty_set_symbol : AxiomCodec IntrinsicAxiomDecode.decode_empty_set_symbol :=
  AxiomCodec.insert empty_set_definition_axiom codec_empty_set

def codec_infinite_predicate : AxiomCodec IntrinsicAxiomDecode.decode_infinite_predicate :=
  AxiomCodec.insert is_infinite_definition_axiom codec_natural_exponentiation

def codec_countable_predicate : AxiomCodec IntrinsicAxiomDecode.decode_countable_predicate :=
  AxiomCodec.insert is_countable_definition_axiom codec_infinite_predicate

def codec_uncountable_predicate : AxiomCodec IntrinsicAxiomDecode.decode_uncountable_predicate :=
  AxiomCodec.insert is_uncountable_definition_axiom codec_countable_predicate

def codec_countably_infinite_predicate : AxiomCodec IntrinsicAxiomDecode.decode_countably_infinite_predicate :=
  AxiomCodec.insert is_countably_infinite_definition_axiom
      codec_uncountable_predicate

def codec_cardinality_classification : AxiomCodec IntrinsicAxiomDecode.decode_cardinality_classification :=
  codec_countably_infinite_predicate

def codec_finite_sequence_space : AxiomCodec IntrinsicAxiomDecode.decode_finite_sequence_space :=
  AxiomCodec.insert finite_sequence_space_definition_axiom
      codec_cardinality_classification

def codec_recursive_sequence_space : AxiomCodec IntrinsicAxiomDecode.decode_recursive_sequence_space :=
  AxiomCodec.insert recursive_sequence_space_definition_axiom
      codec_finite_sequence_space

def codec_omega_recursive_sequence : AxiomCodec IntrinsicAxiomDecode.decode_omega_recursive_sequence :=
  AxiomCodec.insert omega_recursive_sequence_definition_axiom
      codec_recursive_sequence_space

def codec_natural_difference : AxiomCodec IntrinsicAxiomDecode.decode_natural_difference :=
  AxiomCodec.insert natural_difference_definition_axiom
      codec_omega_recursive_sequence

def codec_omega_pair_order : AxiomCodec IntrinsicAxiomDecode.decode_omega_pair_order :=
  AxiomCodec.insert omega_pair_less_definition_axiom codec_natural_difference

def codec_godel_pairing : AxiomCodec IntrinsicAxiomDecode.decode_godel_pairing :=
  AxiomCodec.insert godel_pairing_definition_axiom codec_omega_pair_order

def codec_natural_arithmetic : AxiomCodec IntrinsicAxiomDecode.decode_natural_arithmetic :=
  codec_godel_pairing

def codec_transitive_closure_operator : AxiomCodec IntrinsicAxiomDecode.decode_transitive_closure_operator :=
  AxiomCodec.insert transitive_closure_definition_axiom codec_natural_arithmetic

def codec_finite_hierarchy_operator : AxiomCodec IntrinsicAxiomDecode.decode_finite_hierarchy_operator :=
  AxiomCodec.insert finite_hierarchy_definition_axiom codec_transitive_closure_operator

def codec_finite_universe_operator : AxiomCodec IntrinsicAxiomDecode.decode_finite_universe_operator :=
  AxiomCodec.insert finite_universe_definition_axiom codec_finite_hierarchy_operator

def codec_hereditarily_finite_predicate : AxiomCodec IntrinsicAxiomDecode.decode_hereditarily_finite_predicate :=
  AxiomCodec.insert hereditarily_finite_definition_axiom codec_finite_universe_operator

def codec_finite_subset_collection_separation : AxiomCodec IntrinsicAxiomDecode.decode_finite_subset_collection_separation :=
  AxiomCodec.insert finite_subset_collection_separation_axiom
      codec_hereditarily_finite_predicate

def codec_finite_subset_collection_operator : AxiomCodec IntrinsicAxiomDecode.decode_finite_subset_collection_operator :=
  AxiomCodec.insert finite_subset_collection_definition_axiom
      codec_finite_subset_collection_separation

def codec_hereditarily_finite : AxiomCodec IntrinsicAxiomDecode.decode_hereditarily_finite :=
  codec_finite_subset_collection_operator

def codec_finite_sequence_concatenation : AxiomCodec IntrinsicAxiomDecode.decode_finite_sequence_concatenation :=
  AxiomCodec.insert finite_sequence_concatenation_definition_axiom codec_hereditarily_finite

def codec_nonempty_finite_sequence_space_separation : AxiomCodec IntrinsicAxiomDecode.decode_nonempty_finite_sequence_space_separation :=
  AxiomCodec.insert nonempty_finite_sequence_space_separation_axiom
      codec_finite_sequence_concatenation

def codec_nonempty_finite_sequence_space : AxiomCodec IntrinsicAxiomDecode.decode_nonempty_finite_sequence_space :=
  AxiomCodec.insert nonempty_finite_sequence_space_definition_axiom
      codec_nonempty_finite_sequence_space_separation

def codec_finite_sequence_flatten : AxiomCodec IntrinsicAxiomDecode.decode_finite_sequence_flatten :=
  AxiomCodec.insert finite_sequence_flatten_definition_axiom
      codec_nonempty_finite_sequence_space

def codec_finite_sequence_support : AxiomCodec IntrinsicAxiomDecode.decode_finite_sequence_support :=
  AxiomCodec.union codec_membership_irreflexive <|
      AxiomCodec.union codec_empty_set_symbol <|
        AxiomCodec.union codec_successor_operator <|
          AxiomCodec.union codec_binary_union_operator <|
            AxiomCodec.union codec_ordered_pair_operator <|
              AxiomCodec.union codec_function_application <|
                AxiomCodec.union codec_finite_sequence_flatten
                  codec_finite_sequence_space

def codec_intrinsic_arithmetic_evaluation : AxiomCodec IntrinsicAxiomDecode.decode_intrinsic_arithmetic_evaluation :=
  AxiomCodec.union codec_formal_language_encoding
      codec_finite_sequence_support

def codec_expression_encoding : AxiomCodec IntrinsicAxiomDecode.decode_expression_encoding :=
  AxiomCodec.union codec_membership_irreflexive
      (AxiomCodec.union
        (AxiomCodec.insert free_variable_occurs_definition_axiom
          (AxiomCodec.insert syntax_transform_definition_axiom
            codec_formal_language_encoding))
        codec_empty_set_symbol)

def codec_propositional_axiom_schema : AxiomCodec IntrinsicAxiomDecode.decode_propositional_axiom_schema :=
  AxiomCodec.insert propositional_axiom_schema_definition_axiom
      codec_expression_encoding

def codec_quantifier_axiom_schema : AxiomCodec IntrinsicAxiomDecode.decode_quantifier_axiom_schema :=
  AxiomCodec.insert quantifier_axiom_schema_definition_axiom
      codec_propositional_axiom_schema

def codec_equality_axiom_schema : AxiomCodec IntrinsicAxiomDecode.decode_equality_axiom_schema :=
  AxiomCodec.insert equality_axiom_schema_definition_axiom
      codec_quantifier_axiom_schema

def codec_logical_axiom_code : AxiomCodec IntrinsicAxiomDecode.decode_logical_axiom_code :=
  AxiomCodec.insert logical_axiom_code_definition_axiom
      codec_equality_axiom_schema

def codec_logical_rule_encoding : AxiomCodec IntrinsicAxiomDecode.decode_logical_rule_encoding :=
  AxiomCodec.insert modus_ponens_definition_axiom
      codec_logical_axiom_code

def codec_related_symbol_semantics : AxiomCodec IntrinsicAxiomDecode.decode_related_symbol_semantics :=
  AxiomCodec.insert related_nonlogical_symbol_set_definition_axiom
      codec_logical_rule_encoding

def codec_related_syntax_semantics : AxiomCodec IntrinsicAxiomDecode.decode_related_syntax_semantics :=
  AxiomCodec.insert related_syntax_definition_axiom codec_related_symbol_semantics

def codec_structure_semantics : AxiomCodec IntrinsicAxiomDecode.decode_structure_semantics :=
  AxiomCodec.insert structure_definition_axiom codec_related_syntax_semantics

def codec_term_value_semantics : AxiomCodec IntrinsicAxiomDecode.decode_term_value_semantics :=
  AxiomCodec.insert (term_value_definition_axiom ∧ₘ term_list_value_definition_axiom)
      codec_structure_semantics

def codec_semantic_interpretation : AxiomCodec IntrinsicAxiomDecode.decode_semantic_interpretation :=
  codec_term_value_semantics

def codec_intrinsic_syntax_carrier : AxiomCodec IntrinsicAxiomDecode.decode_intrinsic_syntax_carrier :=
  AxiomCodec.union (AxiomCodec.union codec_subset codec_empty_set_symbol)
      codec_semantic_interpretation

def codec_intrinsic_proof_row : AxiomCodec IntrinsicAxiomDecode.decode_intrinsic_proof_row :=
  AxiomCodec.union codec_intrinsic_syntax_carrier
      codec_finite_sequence_support

def codec_intrinsic_proof : AxiomCodec IntrinsicAxiomDecode.decode_intrinsic_proof :=
  AxiomCodec.union codec_intrinsic_arithmetic_evaluation
      codec_intrinsic_proof_row

end IntrinsicAxiomEncode

def intrinsic_proof_axiom_codec : AxiomCodec intrinsic_proof_axiom_decode :=
  IntrinsicAxiomEncode.codec_intrinsic_proof
end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT
