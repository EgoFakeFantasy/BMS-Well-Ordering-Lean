import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SupportBasisTemplate

/-! # 全部原支撑公理的有限生成性

沿原理论的 insert 与 union 结构组合；十一类无限项参数族由其单一闭模板生成。
各中间定义的目标类型仍是原理论，理论结构发生变化时 Lean 会重新检查这条连接。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SupportAxiomBasis
open Nonlogical.BasicSetTheory SupportAssembly
set_option autoImplicit false
attribute [local implicit_reducible] SupportParameters.Kind.arity

def extensionality : FiniteAxiomBasis extensionality_theory :=
  FiniteAxiomBasis.singleton extensionality_axiom

def pairing : FiniteAxiomBasis pairing_theory :=
  FiniteAxiomBasis.insert pairing_axiom extensionality

def pairing_operator : FiniteAxiomBasis pairing_operator_theory :=
  FiniteAxiomBasis.insert pair_definition_axiom pairing

def union : FiniteAxiomBasis union_theory :=
  FiniteAxiomBasis.insert union_axiom extensionality

def union_operator : FiniteAxiomBasis union_operator_theory :=
  FiniteAxiomBasis.insert union_definition_axiom union

def binary_union_base : FiniteAxiomBasis binary_union_base_theory :=
  FiniteAxiomBasis.union pairing_operator union_operator

def binary_union_operator : FiniteAxiomBasis binary_union_operator_theory :=
  FiniteAxiomBasis.insert
        binary_union_definition_axiom
        binary_union_base

def successor_base : FiniteAxiomBasis successor_base_theory :=
  binary_union_operator

def successor_operator : FiniteAxiomBasis successor_operator_theory :=
  FiniteAxiomBasis.insert successor_definition_axiom successor_base

def singleton_operator : FiniteAxiomBasis singleton_operator_theory :=
  FiniteAxiomBasis.insert singleton_definition_axiom pairing_operator

def ordered_pair_operator : FiniteAxiomBasis ordered_pair_operator_theory :=
  FiniteAxiomBasis.insert ordered_pair_definition_axiom singleton_operator

def relation_function : FiniteAxiomBasis relation_function_theory :=
  FiniteAxiomBasis.insert is_ordered_pair_definition_axiom ordered_pair_operator

def left_projection_operator : FiniteAxiomBasis left_projection_operator_theory :=
  FiniteAxiomBasis.insert left_projection_definition_axiom relation_function

def right_projection_operator : FiniteAxiomBasis right_projection_operator_theory :=
  FiniteAxiomBasis.insert right_projection_definition_axiom left_projection_operator

def relation_base : FiniteAxiomBasis relation_base_theory :=
  FiniteAxiomBasis.union right_projection_operator union_operator

def relation_predicate : FiniteAxiomBasis relation_predicate_theory :=
  FiniteAxiomBasis.insert is_relation_definition_axiom relation_base

def relation_domain : FiniteAxiomBasis relation_domain_theory :=
  FiniteAxiomBasis.congr (FiniteAxiomBasis.union (parameterBasis .domain) relation_predicate) (by
    intro φ
    constructor
    · intro h
      rcases h with ⟨⟨free, args⟩, hφ⟩ | h
      · change Arguments signature [] free (List.replicate 1 SetSort.set) at args
        cases args with | cons t0 tail0 =>
        cases tail0
        exact Or.inl ⟨free, t0, hφ.symm⟩
      · exact Or.inr h
    · intro h
      rcases h with ⟨free, t0, hφ⟩ | h
      · exact Or.inl ⟨⟨free, (.cons t0 .nil)⟩, hφ.symm⟩
      · exact Or.inr h)

def relation_domain_operator : FiniteAxiomBasis relation_domain_operator_theory :=
  FiniteAxiomBasis.insert domain_definition_axiom relation_domain

def relation_range : FiniteAxiomBasis relation_range_theory :=
  FiniteAxiomBasis.congr (FiniteAxiomBasis.union (parameterBasis .range) relation_domain_operator) (by
    intro φ
    constructor
    · intro h
      rcases h with ⟨⟨free, args⟩, hφ⟩ | h
      · change Arguments signature [] free (List.replicate 1 SetSort.set) at args
        cases args with | cons t0 tail0 =>
        cases tail0
        exact Or.inl ⟨free, t0, hφ.symm⟩
      · exact Or.inr h
    · intro h
      rcases h with ⟨free, t0, hφ⟩ | h
      · exact Or.inl ⟨⟨free, (.cons t0 .nil)⟩, hφ.symm⟩
      · exact Or.inr h)

def relation_range_operator : FiniteAxiomBasis relation_range_operator_theory :=
  FiniteAxiomBasis.insert range_definition_axiom relation_range

def subset : FiniteAxiomBasis subset_theory :=
  FiniteAxiomBasis.insert subset_definition_axiom extensionality

def power_set : FiniteAxiomBasis power_set_theory :=
  FiniteAxiomBasis.insert power_set_axiom subset

def power_set_operator : FiniteAxiomBasis power_set_operator_theory :=
  FiniteAxiomBasis.insert power_set_definition_axiom power_set

def cartesian_product_base : FiniteAxiomBasis cartesian_product_base_theory :=
  FiniteAxiomBasis.union ordered_pair_operator
        (FiniteAxiomBasis.union power_set_operator
          binary_union_operator)

def cartesian_product : FiniteAxiomBasis cartesian_product_theory :=
  FiniteAxiomBasis.congr (FiniteAxiomBasis.union (parameterBasis .cartesianProduct) cartesian_product_base) (by
    intro φ
    constructor
    · intro h
      rcases h with ⟨⟨free, args⟩, hφ⟩ | h
      · change Arguments signature [] free (List.replicate 2 SetSort.set) at args
        cases args with | cons t0 tail0 =>
        cases tail0 with | cons t1 tail1 =>
        cases tail1
        exact Or.inl ⟨free, t0, t1, hφ.symm⟩
      · exact Or.inr h
    · intro h
      rcases h with ⟨free, t0, t1, hφ⟩ | h
      · exact Or.inl ⟨⟨free, (.cons t0 (.cons t1 .nil))⟩, hφ.symm⟩
      · exact Or.inr h)

def cartesian_product_operator : FiniteAxiomBasis cartesian_product_operator_theory :=
  FiniteAxiomBasis.insert cartesian_product_definition_axiom cartesian_product

def ordered_pair_reverse_operator : FiniteAxiomBasis ordered_pair_reverse_operator_theory :=
  FiniteAxiomBasis.insert ordered_pair_reverse_definition_axiom
        right_projection_operator

def relation_plane : FiniteAxiomBasis relation_plane_theory :=
  FiniteAxiomBasis.union relation_range_operator
        (FiniteAxiomBasis.union cartesian_product_operator
          ordered_pair_reverse_operator)

def relation_converse : FiniteAxiomBasis relation_converse_theory :=
  FiniteAxiomBasis.congr (FiniteAxiomBasis.union (parameterBasis .converse) relation_plane) (by
    intro φ
    constructor
    · intro h
      rcases h with ⟨⟨free, args⟩, hφ⟩ | h
      · change Arguments signature [] free (List.replicate 1 SetSort.set) at args
        cases args with | cons t0 tail0 =>
        cases tail0
        exact Or.inl ⟨free, t0, hφ.symm⟩
      · exact Or.inr h
    · intro h
      rcases h with ⟨free, t0, hφ⟩ | h
      · exact Or.inl ⟨⟨free, (.cons t0 .nil)⟩, hφ.symm⟩
      · exact Or.inr h)

def relation_converse_operator : FiniteAxiomBasis relation_converse_operator_theory :=
  FiniteAxiomBasis.insert relation_converse_definition_axiom relation_converse

def relation_composition : FiniteAxiomBasis relation_composition_theory :=
  FiniteAxiomBasis.congr (FiniteAxiomBasis.union (parameterBasis .composition) relation_converse_operator) (by
    intro φ
    constructor
    · intro h
      rcases h with ⟨⟨free, args⟩, hφ⟩ | h
      · change Arguments signature [] free (List.replicate 2 SetSort.set) at args
        cases args with | cons t0 tail0 =>
        cases tail0 with | cons t1 tail1 =>
        cases tail1
        exact Or.inl ⟨free, t0, t1, hφ.symm⟩
      · exact Or.inr h
    · intro h
      rcases h with ⟨free, t0, t1, hφ⟩ | h
      · exact Or.inl ⟨⟨free, (.cons t0 (.cons t1 .nil))⟩, hφ.symm⟩
      · exact Or.inr h)

def relation_composition_operator : FiniteAxiomBasis relation_composition_operator_theory :=
  FiniteAxiomBasis.insert relation_composition_definition_axiom
        relation_composition

def equivalence_relation : FiniteAxiomBasis equivalence_relation_theory :=
  FiniteAxiomBasis.insert is_equivalence_relation_definition_axiom
        relation_composition_operator

def function_predicate : FiniteAxiomBasis function_predicate_theory :=
  FiniteAxiomBasis.insert is_function_definition_axiom equivalence_relation

def mapping_predicate : FiniteAxiomBasis mapping_predicate_theory :=
  FiniteAxiomBasis.insert is_mapping_definition_axiom function_predicate

def function_application : FiniteAxiomBasis function_application_theory :=
  FiniteAxiomBasis.insert function_application_definition_axiom mapping_predicate

def injective_predicate : FiniteAxiomBasis injective_predicate_theory :=
  FiniteAxiomBasis.insert is_injective_definition_axiom function_application

def surjective_predicate : FiniteAxiomBasis surjective_predicate_theory :=
  FiniteAxiomBasis.insert is_surjective_definition_axiom injective_predicate

def bijection_predicate : FiniteAxiomBasis bijection_predicate_theory :=
  FiniteAxiomBasis.insert is_bijection_definition_axiom surjective_predicate

def identity : FiniteAxiomBasis identity_theory :=
  FiniteAxiomBasis.congr (FiniteAxiomBasis.union (parameterBasis .identity) bijection_predicate) (by
    intro φ
    constructor
    · intro h
      rcases h with ⟨⟨free, args⟩, hφ⟩ | h
      · change Arguments signature [] free (List.replicate 1 SetSort.set) at args
        cases args with | cons t0 tail0 =>
        cases tail0
        exact Or.inl ⟨free, t0, hφ.symm⟩
      · exact Or.inr h
    · intro h
      rcases h with ⟨free, t0, hφ⟩ | h
      · exact Or.inl ⟨⟨free, (.cons t0 .nil)⟩, hφ.symm⟩
      · exact Or.inr h)

def identity_operator : FiniteAxiomBasis identity_operator_theory :=
  FiniteAxiomBasis.insert identity_definition_axiom identity

def mapping_collection : FiniteAxiomBasis mapping_collection_theory :=
  FiniteAxiomBasis.congr (FiniteAxiomBasis.union (parameterBasis .mappingCollection) identity_operator) (by
    intro φ
    constructor
    · intro h
      rcases h with ⟨⟨free, args⟩, hφ⟩ | h
      · change Arguments signature [] free (List.replicate 2 SetSort.set) at args
        cases args with | cons t0 tail0 =>
        cases tail0 with | cons t1 tail1 =>
        cases tail1
        exact Or.inl ⟨free, t0, t1, hφ.symm⟩
      · exact Or.inr h
    · intro h
      rcases h with ⟨free, t0, t1, hφ⟩ | h
      · exact Or.inl ⟨⟨free, (.cons t0 (.cons t1 .nil))⟩, hφ.symm⟩
      · exact Or.inr h)

def mapping_collection_operator : FiniteAxiomBasis mapping_collection_operator_theory :=
  FiniteAxiomBasis.insert mapping_collection_definition_axiom mapping_collection

def transitive_set : FiniteAxiomBasis transitive_set_theory :=
  FiniteAxiomBasis.insert is_transitive_set_definition_axiom
        mapping_collection_operator

def membership_relation : FiniteAxiomBasis membership_relation_theory :=
  FiniteAxiomBasis.insert membership_relation_predicate.separation_axiom
        transitive_set

def membership_relation_operator : FiniteAxiomBasis membership_relation_operator_theory :=
  FiniteAxiomBasis.insert membership_relation_definition_axiom
        membership_relation

def linear_order : FiniteAxiomBasis linear_order_theory :=
  FiniteAxiomBasis.insert is_linear_order_definition_axiom
        membership_relation_operator

def order_isomorphism : FiniteAxiomBasis order_isomorphism_theory :=
  FiniteAxiomBasis.insert is_order_isomorphism_definition_axiom linear_order

def order_isomorphic : FiniteAxiomBasis order_isomorphic_theory :=
  FiniteAxiomBasis.insert is_order_isomorphic_definition_axiom order_isomorphism

def order_embedding : FiniteAxiomBasis order_embedding_theory :=
  FiniteAxiomBasis.insert is_order_embedding_definition_axiom order_isomorphic

def order_embeddable : FiniteAxiomBasis order_embeddable_theory :=
  FiniteAxiomBasis.insert is_order_embeddable_definition_axiom order_embedding

def natural_discrete_linear_order : FiniteAxiomBasis natural_discrete_linear_order_theory :=
  FiniteAxiomBasis.insert is_natural_discrete_linear_order_definition_axiom
        order_embeddable

def well_order : FiniteAxiomBasis well_order_theory :=
  FiniteAxiomBasis.insert well_order_definition_axiom
        natural_discrete_linear_order

def finite_ordinal : FiniteAxiomBasis finite_ordinal_theory :=
  well_order

def relation_image_separation : FiniteAxiomBasis relation_image_separation_theory :=
  FiniteAxiomBasis.insert relation_image_separation_axiom finite_ordinal

def image_operator : FiniteAxiomBasis image_operator_theory :=
  FiniteAxiomBasis.insert image_definition_axiom relation_image_separation

def restriction_operator : FiniteAxiomBasis restriction_operator_theory :=
  FiniteAxiomBasis.insert restriction_definition_axiom image_operator

def minimum_linear_order : FiniteAxiomBasis minimum_linear_order_theory :=
  FiniteAxiomBasis.insert minimum_linear_order_definition_axiom restriction_operator

def minimum_natural_order : FiniteAxiomBasis minimum_natural_order_theory :=
  FiniteAxiomBasis.insert minimum_natural_order_definition_axiom minimum_linear_order

def order_operator : FiniteAxiomBasis order_operator_theory :=
  FiniteAxiomBasis.insert maximum_natural_order_definition_axiom minimum_natural_order

def minimum_difference : FiniteAxiomBasis minimum_difference_theory :=
  FiniteAxiomBasis.insert minimum_difference_definition_axiom order_operator

def index_order_separation : FiniteAxiomBasis index_order_separation_theory :=
  FiniteAxiomBasis.congr (FiniteAxiomBasis.union (parameterBasis .indexOrder) minimum_difference) (by
    intro φ
    constructor
    · intro h
      rcases h with ⟨⟨free, args⟩, hφ⟩ | h
      · change Arguments signature [] free (List.replicate 4 SetSort.set) at args
        cases args with | cons t0 tail0 =>
        cases tail0 with | cons t1 tail1 =>
        cases tail1 with | cons t2 tail2 =>
        cases tail2 with | cons t3 tail3 =>
        cases tail3
        exact Or.inl ⟨free, t0, t1, t2, t3, hφ.symm⟩
      · exact Or.inr h
    · intro h
      rcases h with ⟨free, t0, t1, t2, t3, hφ⟩ | h
      · exact Or.inl ⟨⟨free, (.cons t0 (.cons t1 (.cons t2 (.cons t3 .nil))))⟩, hφ.symm⟩
      · exact Or.inr h)

def index_order : FiniteAxiomBasis index_order_theory :=
  FiniteAxiomBasis.insert index_order_definition_axiom index_order_separation

def power_set_bijection_separation : FiniteAxiomBasis power_set_bijection_separation_theory :=
  FiniteAxiomBasis.congr (FiniteAxiomBasis.union (parameterBasis .powerSetBijection) index_order) (by
    intro φ
    constructor
    · intro h
      rcases h with ⟨⟨free, args⟩, hφ⟩ | h
      · change Arguments signature [] free (List.replicate 1 SetSort.set) at args
        cases args with | cons t0 tail0 =>
        cases tail0
        exact Or.inl ⟨free, t0, hφ.symm⟩
      · exact Or.inr h
    · intro h
      rcases h with ⟨free, t0, hφ⟩ | h
      · exact Or.inl ⟨⟨free, (.cons t0 .nil)⟩, hφ.symm⟩
      · exact Or.inr h)

def power_set_bijection : FiniteAxiomBasis power_set_bijection_theory :=
  FiniteAxiomBasis.insert power_set_bijection_definition_axiom
        power_set_bijection_separation

def symmetric_difference_separation : FiniteAxiomBasis symmetric_difference_separation_theory :=
  FiniteAxiomBasis.congr (FiniteAxiomBasis.union (parameterBasis .symmetricDifference) power_set_bijection) (by
    intro φ
    constructor
    · intro h
      rcases h with ⟨⟨free, args⟩, hφ⟩ | h
      · change Arguments signature [] free (List.replicate 2 SetSort.set) at args
        cases args with | cons t0 tail0 =>
        cases tail0 with | cons t1 tail1 =>
        cases tail1
        exact Or.inl ⟨free, t0, t1, hφ.symm⟩
      · exact Or.inr h
    · intro h
      rcases h with ⟨free, t0, t1, hφ⟩ | h
      · exact Or.inl ⟨⟨free, (.cons t0 (.cons t1 .nil))⟩, hφ.symm⟩
      · exact Or.inr h)

def symmetric_difference : FiniteAxiomBasis symmetric_difference_theory :=
  FiniteAxiomBasis.insert symmetric_difference_definition_axiom
        symmetric_difference_separation

def finite_predicate : FiniteAxiomBasis finite_predicate_theory :=
  FiniteAxiomBasis.insert is_finite_definition_axiom symmetric_difference

def equinumerous_predicate : FiniteAxiomBasis equinumerous_predicate_theory :=
  FiniteAxiomBasis.insert is_equinumerous_definition_axiom finite_predicate

def cardinality_leq_predicate : FiniteAxiomBasis cardinality_leq_predicate_theory :=
  FiniteAxiomBasis.insert cardinality_leq_definition_axiom
        equinumerous_predicate

def cardinality_strict_less_predicate : FiniteAxiomBasis cardinality_strict_less_predicate_theory :=
  FiniteAxiomBasis.insert cardinality_strict_less_definition_axiom
        cardinality_leq_predicate

def dedekind_finite_predicate : FiniteAxiomBasis dedekind_finite_predicate_theory :=
  FiniteAxiomBasis.insert is_dedekind_finite_definition_axiom
        cardinality_strict_less_predicate

def basic_finite : FiniteAxiomBasis basic_finite_theory :=
  dedekind_finite_predicate

def infinity_axiom : FiniteAxiomBasis infinity_axiom_theory :=
  FiniteAxiomBasis.insert Nonlogical.BasicSetTheory.infinity_axiom basic_finite

def inductive_set : FiniteAxiomBasis inductive_set_theory :=
  FiniteAxiomBasis.insert is_inductive_set_definition_axiom infinity_axiom

def inductive_core_separation : FiniteAxiomBasis inductive_core_separation_theory :=
  FiniteAxiomBasis.congr (FiniteAxiomBasis.union (parameterBasis .inductiveCore) inductive_set) (by
    intro φ
    constructor
    · intro h
      rcases h with ⟨⟨free, args⟩, hφ⟩ | h
      · change Arguments signature [] free (List.replicate 1 SetSort.set) at args
        cases args with | cons t0 tail0 =>
        cases tail0
        exact Or.inl ⟨free, t0, hφ.symm⟩
      · exact Or.inr h
    · intro h
      rcases h with ⟨free, t0, hφ⟩ | h
      · exact Or.inl ⟨⟨free, (.cons t0 .nil)⟩, hφ.symm⟩
      · exact Or.inr h)

def inductive_core : FiniteAxiomBasis inductive_core_theory :=
  FiniteAxiomBasis.insert inductive_core_definition_axiom
        inductive_core_separation

def infinity : FiniteAxiomBasis infinity_theory :=
  FiniteAxiomBasis.insert omega_definition_axiom inductive_core

def unbounded_subset : FiniteAxiomBasis unbounded_subset_theory :=
  FiniteAxiomBasis.insert unbounded_subset_definition_axiom infinity

def bounded_subset : FiniteAxiomBasis bounded_subset_theory :=
  FiniteAxiomBasis.insert bounded_subset_definition_axiom unbounded_subset

def natural_order_type : FiniteAxiomBasis natural_order_type_theory :=
  FiniteAxiomBasis.insert natural_order_type_definition_axiom bounded_subset

def natural_subset_type : FiniteAxiomBasis natural_subset_type_theory :=
  FiniteAxiomBasis.insert natural_subset_type_definition_axiom natural_order_type

def natural_set : FiniteAxiomBasis natural_set_theory :=
  natural_subset_type

def natural_addition : FiniteAxiomBasis natural_addition_theory :=
  FiniteAxiomBasis.insert natural_addition_definition_axiom natural_set

def natural_multiplication : FiniteAxiomBasis natural_multiplication_theory :=
  FiniteAxiomBasis.insert natural_multiplication_definition_axiom
        natural_addition

def natural_exponentiation : FiniteAxiomBasis natural_exponentiation_theory :=
  FiniteAxiomBasis.insert natural_exponentiation_definition_axiom
        natural_multiplication

def godel_pairing_core : FiniteAxiomBasis godel_pairing_core_theory :=
  FiniteAxiomBasis.insert godel_pairing_definition_axiom
        natural_exponentiation

def natural_exponentiation_bound : FiniteAxiomBasis natural_exponentiation_bound_theory :=
  FiniteAxiomBasis.insert natural_exponentiation_index_bound_axiom
        (FiniteAxiomBasis.insert natural_exponent_product_index_bound_axiom
          godel_pairing_core)

def natural_addition_bound : FiniteAxiomBasis natural_addition_bound_theory :=
  FiniteAxiomBasis.insert natural_addition_upper_bound_axiom
        (FiniteAxiomBasis.insert natural_positive_left_addition_strict_bound_axiom
          (FiniteAxiomBasis.insert natural_le_lt_transitivity_axiom
            (FiniteAxiomBasis.insert natural_godel_pairing_coordinate_bound_axiom
              natural_exponentiation_bound)))

def formal_language_encoding : FiniteAxiomBasis formal_language_encoding_theory :=
  FiniteAxiomBasis.insert structural_syntax_definition_axiom
        (FiniteAxiomBasis.union successor_operator natural_addition_bound)

def membership_irreflexive : FiniteAxiomBasis membership_irreflexive_theory :=
  FiniteAxiomBasis.singleton membership_irreflexive_axiom

def empty_set : FiniteAxiomBasis empty_set_theory :=
  FiniteAxiomBasis.insert (empty_predicate (free := [])).separation_axiom
        extensionality

def empty_set_symbol : FiniteAxiomBasis empty_set_symbol_theory :=
  FiniteAxiomBasis.insert empty_set_definition_axiom empty_set

def infinite_predicate : FiniteAxiomBasis infinite_predicate_theory :=
  FiniteAxiomBasis.insert is_infinite_definition_axiom natural_exponentiation

def countable_predicate : FiniteAxiomBasis countable_predicate_theory :=
  FiniteAxiomBasis.insert is_countable_definition_axiom infinite_predicate

def uncountable_predicate : FiniteAxiomBasis uncountable_predicate_theory :=
  FiniteAxiomBasis.insert is_uncountable_definition_axiom countable_predicate

def countably_infinite_predicate : FiniteAxiomBasis countably_infinite_predicate_theory :=
  FiniteAxiomBasis.insert is_countably_infinite_definition_axiom
        uncountable_predicate

def cardinality_classification : FiniteAxiomBasis cardinality_classification_theory :=
  countably_infinite_predicate

def finite_sequence_space : FiniteAxiomBasis finite_sequence_space_theory :=
  FiniteAxiomBasis.insert finite_sequence_space_definition_axiom
        cardinality_classification

def recursive_sequence_space : FiniteAxiomBasis recursive_sequence_space_theory :=
  FiniteAxiomBasis.insert recursive_sequence_space_definition_axiom
        finite_sequence_space

def omega_recursive_sequence : FiniteAxiomBasis omega_recursive_sequence_theory :=
  FiniteAxiomBasis.insert omega_recursive_sequence_definition_axiom
        recursive_sequence_space

def natural_difference : FiniteAxiomBasis natural_difference_theory :=
  FiniteAxiomBasis.insert natural_difference_definition_axiom
        omega_recursive_sequence

def omega_pair_order : FiniteAxiomBasis omega_pair_order_theory :=
  FiniteAxiomBasis.insert omega_pair_less_definition_axiom natural_difference

def godel_pairing : FiniteAxiomBasis godel_pairing_theory :=
  FiniteAxiomBasis.insert godel_pairing_definition_axiom omega_pair_order

def natural_arithmetic : FiniteAxiomBasis natural_arithmetic_theory :=
  godel_pairing

def transitive_closure_operator : FiniteAxiomBasis transitive_closure_operator_theory :=
  FiniteAxiomBasis.insert transitive_closure_definition_axiom natural_arithmetic

def finite_hierarchy_operator : FiniteAxiomBasis finite_hierarchy_operator_theory :=
  FiniteAxiomBasis.insert finite_hierarchy_definition_axiom transitive_closure_operator

def finite_universe_operator : FiniteAxiomBasis finite_universe_operator_theory :=
  FiniteAxiomBasis.insert finite_universe_definition_axiom finite_hierarchy_operator

def hereditarily_finite_predicate : FiniteAxiomBasis hereditarily_finite_predicate_theory :=
  FiniteAxiomBasis.insert hereditarily_finite_definition_axiom finite_universe_operator

def finite_subset_collection_separation : FiniteAxiomBasis finite_subset_collection_separation_theory :=
  FiniteAxiomBasis.insert finite_subset_collection_separation_axiom
        hereditarily_finite_predicate

def finite_subset_collection_operator : FiniteAxiomBasis finite_subset_collection_operator_theory :=
  FiniteAxiomBasis.insert finite_subset_collection_definition_axiom
        finite_subset_collection_separation

def hereditarily_finite : FiniteAxiomBasis hereditarily_finite_theory :=
  finite_subset_collection_operator

def finite_sequence_concatenation : FiniteAxiomBasis finite_sequence_concatenation_theory :=
  FiniteAxiomBasis.insert finite_sequence_concatenation_definition_axiom hereditarily_finite

def nonempty_finite_sequence_space_separation : FiniteAxiomBasis nonempty_finite_sequence_space_separation_theory :=
  FiniteAxiomBasis.insert nonempty_finite_sequence_space_separation_axiom
        finite_sequence_concatenation

def nonempty_finite_sequence_space : FiniteAxiomBasis nonempty_finite_sequence_space_theory :=
  FiniteAxiomBasis.insert nonempty_finite_sequence_space_definition_axiom
        nonempty_finite_sequence_space_separation

def finite_sequence_flatten : FiniteAxiomBasis finite_sequence_flatten_theory :=
  FiniteAxiomBasis.insert finite_sequence_flatten_definition_axiom
        nonempty_finite_sequence_space

def finite_sequence_support : FiniteAxiomBasis finite_sequence_support_theory :=
  FiniteAxiomBasis.union membership_irreflexive <|
        FiniteAxiomBasis.union empty_set_symbol <|
          FiniteAxiomBasis.union successor_operator <|
            FiniteAxiomBasis.union binary_union_operator <|
              FiniteAxiomBasis.union ordered_pair_operator <|
                FiniteAxiomBasis.union function_application <|
                  FiniteAxiomBasis.union finite_sequence_flatten
                    finite_sequence_space

def intrinsic_arithmetic_evaluation : FiniteAxiomBasis intrinsic_arithmetic_evaluation_theory :=
  FiniteAxiomBasis.union formal_language_encoding
        finite_sequence_support

def expression_encoding : FiniteAxiomBasis expression_encoding_theory :=
  FiniteAxiomBasis.union membership_irreflexive
        (FiniteAxiomBasis.union
          (FiniteAxiomBasis.insert free_variable_occurs_definition_axiom
            (FiniteAxiomBasis.insert syntax_transform_definition_axiom
              formal_language_encoding))
          empty_set_symbol)

def propositional_axiom_schema : FiniteAxiomBasis propositional_axiom_schema_theory :=
  FiniteAxiomBasis.insert propositional_axiom_schema_definition_axiom
        expression_encoding

def quantifier_axiom_schema : FiniteAxiomBasis quantifier_axiom_schema_theory :=
  FiniteAxiomBasis.insert quantifier_axiom_schema_definition_axiom
        propositional_axiom_schema

def equality_axiom_schema : FiniteAxiomBasis equality_axiom_schema_theory :=
  FiniteAxiomBasis.insert equality_axiom_schema_definition_axiom
        quantifier_axiom_schema

def logical_axiom_code : FiniteAxiomBasis logical_axiom_code_theory :=
  FiniteAxiomBasis.insert logical_axiom_code_definition_axiom
        equality_axiom_schema

def logical_rule_encoding : FiniteAxiomBasis logical_rule_encoding_theory :=
  FiniteAxiomBasis.insert modus_ponens_definition_axiom
        logical_axiom_code

def related_symbol_semantics : FiniteAxiomBasis related_symbol_semantics_theory :=
  FiniteAxiomBasis.insert related_nonlogical_symbol_set_definition_axiom
        logical_rule_encoding

def related_syntax_semantics : FiniteAxiomBasis related_syntax_semantics_theory :=
  FiniteAxiomBasis.insert related_syntax_definition_axiom related_symbol_semantics

def structure_semantics : FiniteAxiomBasis structure_semantics_theory :=
  FiniteAxiomBasis.insert structure_definition_axiom related_syntax_semantics

def term_value_semantics : FiniteAxiomBasis term_value_semantics_theory :=
  FiniteAxiomBasis.insert (term_value_definition_axiom ∧ₘ term_list_value_definition_axiom)
        structure_semantics

def semantic_interpretation : FiniteAxiomBasis semantic_interpretation_theory :=
  term_value_semantics

def intrinsic_syntax_carrier : FiniteAxiomBasis intrinsic_syntax_carrier_theory :=
  FiniteAxiomBasis.union (FiniteAxiomBasis.union subset empty_set_symbol)
        semantic_interpretation

def intrinsic_proof_row : FiniteAxiomBasis intrinsic_proof_row_theory :=
  FiniteAxiomBasis.union intrinsic_syntax_carrier
        finite_sequence_support

def intrinsic_proof : FiniteAxiomBasis intrinsic_proof_theory :=
  FiniteAxiomBasis.union intrinsic_arithmetic_evaluation
        intrinsic_proof_row

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SupportAxiomBasis
