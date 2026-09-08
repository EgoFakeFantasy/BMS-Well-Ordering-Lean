import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteAxiomModels
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SupportAxiomBasis
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureFinalOperations
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureFinalInfinity
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureFinalSeparation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureFinalRelations
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureFinalExtrema
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureFinalSyntax

/-! # 裸 ZFC 的最终扩张满足整个原支撑理论

逐项消费原闭句的验证定理，再沿原理论的有限公理基结构组合。
参数分离族由闭模板的普通推导覆盖，因此结论包含所有参数实例。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSupportModels
open PureModel Nonlogical.BasicSetTheory PureFinalTransfer
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
variable {ℳ : Structure.{0,0,0,x} ℒ}

private theorem parameter_models (hℳ : Theory.Models ℳ theory) (kind : SupportParameters.Kind) :
    Theory.Models (E hℳ).model (SupportAssembly.parameterBasis kind).theory := by
  intro φ hφ
  have hEqual : φ = SupportAssembly.closedTemplate kind := List.mem_singleton.mp hφ
  exact hEqual.symm ▸ PureSupportSeparation.parameter_template hℳ kind

private theorem extensionality_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.extensionality.theory :=
  (FiniteAxiomBasis.singleton_models (PureFinalBasic.extensionality_axiom hℳ))

private theorem pairing_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.pairing.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalBasic.pairing_exists hℳ) (extensionality_models hℳ))

private theorem pairing_operator_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.pairing_operator.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalBasic.pairing hℳ) (pairing_models hℳ))

private theorem union_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.union.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalBasic.union_exists_axiom hℳ) (extensionality_models hℳ))

private theorem union_operator_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.union_operator.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalBasic.union_definition hℳ) (union_models hℳ))

private theorem binary_union_base_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.binary_union_base.theory :=
  (FiniteAxiomBasis.union_models (pairing_operator_models hℳ) (union_operator_models hℳ))

private theorem binary_union_operator_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.binary_union_operator.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalBasic.binary_union hℳ) (binary_union_base_models hℳ))

private theorem successor_base_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.successor_base.theory :=
  (binary_union_operator_models hℳ)

private theorem successor_operator_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.successor_operator.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalBasic.successor hℳ) (successor_base_models hℳ))

private theorem singleton_operator_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.singleton_operator.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalBasic.singleton hℳ) (pairing_operator_models hℳ))

private theorem ordered_pair_operator_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.ordered_pair_operator.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalPairs.ordered_pair hℳ) (singleton_operator_models hℳ))

private theorem relation_function_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.relation_function.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalPairs.is_ordered_pair hℳ) (ordered_pair_operator_models hℳ))

private theorem left_projection_operator_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.left_projection_operator.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalPairs.left_projection hℳ) (relation_function_models hℳ))

private theorem right_projection_operator_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.right_projection_operator.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalPairs.right_projection hℳ) (left_projection_operator_models hℳ))

private theorem relation_base_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.relation_base.theory :=
  (FiniteAxiomBasis.union_models (right_projection_operator_models hℳ) (union_operator_models hℳ))

private theorem relation_predicate_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.relation_predicate.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalPairs.is_relation hℳ) (relation_base_models hℳ))

private theorem relation_domain_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.relation_domain.theory :=
  (FiniteAxiomBasis.union_models (parameter_models hℳ .domain) (relation_predicate_models hℳ))

private theorem relation_domain_operator_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.relation_domain_operator.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalMappings.domain hℳ) (relation_domain_models hℳ))

private theorem relation_range_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.relation_range.theory :=
  (FiniteAxiomBasis.union_models (parameter_models hℳ .range) (relation_domain_operator_models hℳ))

private theorem relation_range_operator_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.relation_range_operator.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalMappings.range hℳ) (relation_range_models hℳ))

private theorem subset_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.subset.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalBasic.subset hℳ) (extensionality_models hℳ))

private theorem power_set_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.power_set.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalBasic.power_exists_axiom hℳ) (subset_models hℳ))

private theorem power_set_operator_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.power_set_operator.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalBasic.power_definition hℳ) (power_set_models hℳ))

private theorem cartesian_product_base_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.cartesian_product_base.theory :=
  (FiniteAxiomBasis.union_models (ordered_pair_operator_models hℳ) (FiniteAxiomBasis.union_models (power_set_operator_models hℳ) (binary_union_operator_models hℳ)))

private theorem cartesian_product_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.cartesian_product.theory :=
  (FiniteAxiomBasis.union_models (parameter_models hℳ .cartesianProduct) (cartesian_product_base_models hℳ))

private theorem cartesian_product_operator_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.cartesian_product_operator.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalCollections.cartesian_product hℳ) (cartesian_product_models hℳ))

private theorem ordered_pair_reverse_operator_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.ordered_pair_reverse_operator.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalPairs.reverse hℳ) (right_projection_operator_models hℳ))

private theorem relation_plane_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.relation_plane.theory :=
  (FiniteAxiomBasis.union_models (relation_range_operator_models hℳ) (FiniteAxiomBasis.union_models (cartesian_product_operator_models hℳ) (ordered_pair_reverse_operator_models hℳ)))

private theorem relation_converse_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.relation_converse.theory :=
  (FiniteAxiomBasis.union_models (parameter_models hℳ .converse) (relation_plane_models hℳ))

private theorem relation_converse_operator_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.relation_converse_operator.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalOperations.converse hℳ) (relation_converse_models hℳ))

private theorem relation_composition_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.relation_composition.theory :=
  (FiniteAxiomBasis.union_models (parameter_models hℳ .composition) (relation_converse_operator_models hℳ))

private theorem relation_composition_operator_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.relation_composition_operator.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalOperations.composition hℳ) (relation_composition_models hℳ))

private theorem equivalence_relation_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.equivalence_relation.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalRelations.is_equivalence_relation hℳ) (relation_composition_operator_models hℳ))

private theorem function_predicate_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.function_predicate.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalMappings.is_function hℳ) (equivalence_relation_models hℳ))

private theorem mapping_predicate_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.mapping_predicate.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalMappings.is_mapping hℳ) (function_predicate_models hℳ))

private theorem function_application_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.function_application.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalMappings.application hℳ) (mapping_predicate_models hℳ))

private theorem injective_predicate_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.injective_predicate.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalRelations.is_injective hℳ) (function_application_models hℳ))

private theorem surjective_predicate_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.surjective_predicate.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalRelations.is_surjective hℳ) (injective_predicate_models hℳ))

private theorem bijection_predicate_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.bijection_predicate.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalRelations.is_bijection hℳ) (surjective_predicate_models hℳ))

private theorem identity_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.identity.theory :=
  (FiniteAxiomBasis.union_models (parameter_models hℳ .identity) (bijection_predicate_models hℳ))

private theorem identity_operator_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.identity_operator.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalCollections.identity hℳ) (identity_models hℳ))

private theorem mapping_collection_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.mapping_collection.theory :=
  (FiniteAxiomBasis.union_models (parameter_models hℳ .mappingCollection) (identity_operator_models hℳ))

private theorem mapping_collection_operator_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.mapping_collection_operator.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalCollections.mapping_collection hℳ) (mapping_collection_models hℳ))

private theorem transitive_set_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.transitive_set.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalRelations.is_transitive_set hℳ) (mapping_collection_operator_models hℳ))

private theorem membership_relation_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.membership_relation.theory :=
  (FiniteAxiomBasis.insert_models (PureSupportSeparation.separation_axiom hℳ membership_relation_predicate) (transitive_set_models hℳ))

private theorem membership_relation_operator_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.membership_relation_operator.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalOperations.membership_relation hℳ) (membership_relation_models hℳ))

private theorem linear_order_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.linear_order.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalRelations.is_linear_order hℳ) (membership_relation_operator_models hℳ))

private theorem order_isomorphism_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.order_isomorphism.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalRelations.is_order_isomorphism hℳ) (linear_order_models hℳ))

private theorem order_isomorphic_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.order_isomorphic.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalRelations.is_order_isomorphic hℳ) (order_isomorphism_models hℳ))

private theorem order_embedding_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.order_embedding.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalRelations.is_order_embedding hℳ) (order_isomorphic_models hℳ))

private theorem order_embeddable_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.order_embeddable.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalRelations.is_order_embeddable hℳ) (order_embedding_models hℳ))

private theorem natural_discrete_linear_order_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.natural_discrete_linear_order.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalRelations.is_natural_discrete_linear_order hℳ) (order_embeddable_models hℳ))

private theorem well_order_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.well_order.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalRelations.well_order hℳ) (natural_discrete_linear_order_models hℳ))

private theorem finite_ordinal_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.finite_ordinal.theory :=
  (well_order_models hℳ)

private theorem relation_image_separation_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.relation_image_separation.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalSeparation.relation_image hℳ) (finite_ordinal_models hℳ))

private theorem image_operator_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.image_operator.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalOperations.image hℳ) (relation_image_separation_models hℳ))

private theorem restriction_operator_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.restriction_operator.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalCollections.restriction hℳ) (image_operator_models hℳ))

private theorem minimum_linear_order_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.minimum_linear_order.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalExtrema.minimum_linear_order hℳ) (restriction_operator_models hℳ))

private theorem minimum_natural_order_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.minimum_natural_order.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalExtrema.minimum_natural_order hℳ) (minimum_linear_order_models hℳ))

private theorem order_operator_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.order_operator.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalExtrema.maximum_natural_order hℳ) (minimum_natural_order_models hℳ))

private theorem minimum_difference_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.minimum_difference.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalConstructions.minimum_difference hℳ) (order_operator_models hℳ))

private theorem index_order_separation_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.index_order_separation.theory :=
  (FiniteAxiomBasis.union_models (parameter_models hℳ .indexOrder) (minimum_difference_models hℳ))

private theorem index_order_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.index_order.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalConstructions.index_order hℳ) (index_order_separation_models hℳ))

private theorem power_set_bijection_separation_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.power_set_bijection_separation.theory :=
  (FiniteAxiomBasis.union_models (parameter_models hℳ .powerSetBijection) (index_order_models hℳ))

private theorem power_set_bijection_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.power_set_bijection.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalConstructions.power_set_bijection hℳ) (power_set_bijection_separation_models hℳ))

private theorem symmetric_difference_separation_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.symmetric_difference_separation.theory :=
  (FiniteAxiomBasis.union_models (parameter_models hℳ .symmetricDifference) (power_set_bijection_models hℳ))

private theorem symmetric_difference_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.symmetric_difference.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalOperations.symmetric_difference hℳ) (symmetric_difference_separation_models hℳ))

private theorem finite_predicate_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.finite_predicate.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalRelations.is_finite hℳ) (symmetric_difference_models hℳ))

private theorem equinumerous_predicate_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.equinumerous_predicate.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalRelations.is_equinumerous hℳ) (finite_predicate_models hℳ))

private theorem cardinality_leq_predicate_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.cardinality_leq_predicate.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalRelations.cardinality_leq hℳ) (equinumerous_predicate_models hℳ))

private theorem cardinality_strict_less_predicate_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.cardinality_strict_less_predicate.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalRelations.cardinality_strict_less hℳ) (cardinality_leq_predicate_models hℳ))

private theorem dedekind_finite_predicate_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.dedekind_finite_predicate.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalRelations.is_dedekind_finite hℳ) (cardinality_strict_less_predicate_models hℳ))

private theorem basic_finite_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.basic_finite.theory :=
  (dedekind_finite_predicate_models hℳ)

private theorem infinity_axiom_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.infinity_axiom.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalInfinity.infinity hℳ) (basic_finite_models hℳ))

private theorem inductive_set_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.inductive_set.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalRelations.is_inductive_set hℳ) (infinity_axiom_models hℳ))

private theorem inductive_core_separation_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.inductive_core_separation.theory :=
  (FiniteAxiomBasis.union_models (parameter_models hℳ .inductiveCore) (inductive_set_models hℳ))

private theorem inductive_core_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.inductive_core.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalInfinity.inductive_core hℳ) (inductive_core_separation_models hℳ))

private theorem infinity_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.infinity.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalInfinity.omega hℳ) (inductive_core_models hℳ))

private theorem unbounded_subset_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.unbounded_subset.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalRelations.unbounded_subset hℳ) (infinity_models hℳ))

private theorem bounded_subset_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.bounded_subset.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalRelations.bounded_subset hℳ) (unbounded_subset_models hℳ))

private theorem natural_order_type_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.natural_order_type.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalConstructions.natural_order_type hℳ) (bounded_subset_models hℳ))

private theorem natural_subset_type_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.natural_subset_type.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalConstructions.natural_subset_type hℳ) (natural_order_type_models hℳ))

private theorem natural_set_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.natural_set.theory :=
  (natural_subset_type_models hℳ)

private theorem natural_addition_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.natural_addition.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalConstructions.natural_addition hℳ) (natural_set_models hℳ))

private theorem natural_multiplication_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.natural_multiplication.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalConstructions.natural_multiplication hℳ) (natural_addition_models hℳ))

private theorem natural_exponentiation_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.natural_exponentiation.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalConstructions.natural_exponentiation hℳ) (natural_multiplication_models hℳ))

private theorem godel_pairing_core_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.godel_pairing_core.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalConstructions.godel_pairing hℳ) (natural_exponentiation_models hℳ))

private theorem natural_exponentiation_bound_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.natural_exponentiation_bound.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalArithmetic.exponent_axiom hℳ) (FiniteAxiomBasis.insert_models (PureFinalArithmetic.exponent_product_axiom hℳ) (godel_pairing_core_models hℳ)))

private theorem natural_addition_bound_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.natural_addition_bound.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalArithmetic.addition_upper_axiom hℳ) (FiniteAxiomBasis.insert_models (PureFinalArithmetic.positive_addition_axiom hℳ) (FiniteAxiomBasis.insert_models (PureFinalArithmetic.transitivity_axiom hℳ) (FiniteAxiomBasis.insert_models (PureFinalArithmetic.pairing_axiom hℳ) (natural_exponentiation_bound_models hℳ)))))

private theorem formal_language_encoding_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.formal_language_encoding.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalSyntax.structural_syntax hℳ) (FiniteAxiomBasis.union_models (successor_operator_models hℳ) (natural_addition_bound_models hℳ)))

private theorem membership_irreflexive_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.membership_irreflexive.theory :=
  (FiniteAxiomBasis.singleton_models (PureFinalBasic.irreflexivity hℳ))

private theorem empty_set_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.empty_set.theory :=
  (FiniteAxiomBasis.insert_models (PureSupportSeparation.separation_axiom hℳ (empty_predicate (free := []))) (extensionality_models hℳ))

private theorem empty_set_symbol_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.empty_set_symbol.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalBasic.empty_set hℳ) (empty_set_models hℳ))

private theorem infinite_predicate_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.infinite_predicate.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalRelations.is_infinite hℳ) (natural_exponentiation_models hℳ))

private theorem countable_predicate_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.countable_predicate.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalRelations.is_countable hℳ) (infinite_predicate_models hℳ))

private theorem uncountable_predicate_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.uncountable_predicate.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalRelations.is_uncountable hℳ) (countable_predicate_models hℳ))

private theorem countably_infinite_predicate_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.countably_infinite_predicate.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalRelations.is_countably_infinite hℳ) (uncountable_predicate_models hℳ))

private theorem cardinality_classification_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.cardinality_classification.theory :=
  (countably_infinite_predicate_models hℳ)

private theorem finite_sequence_space_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.finite_sequence_space.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalConstructions.finite_sequence_space hℳ) (cardinality_classification_models hℳ))

private theorem recursive_sequence_space_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.recursive_sequence_space.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalConstructions.recursive_sequence_space hℳ) (finite_sequence_space_models hℳ))

private theorem omega_recursive_sequence_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.omega_recursive_sequence.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalConstructions.omega_recursive_sequence hℳ) (recursive_sequence_space_models hℳ))

private theorem natural_difference_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.natural_difference.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalConstructions.natural_difference hℳ) (omega_recursive_sequence_models hℳ))

private theorem omega_pair_order_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.omega_pair_order.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalRelations.omega_pair_less hℳ) (natural_difference_models hℳ))

private theorem godel_pairing_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.godel_pairing.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalConstructions.godel_pairing hℳ) (omega_pair_order_models hℳ))

private theorem natural_arithmetic_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.natural_arithmetic.theory :=
  (godel_pairing_models hℳ)

private theorem transitive_closure_operator_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.transitive_closure_operator.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalConstructions.transitive_closure hℳ) (natural_arithmetic_models hℳ))

private theorem finite_hierarchy_operator_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.finite_hierarchy_operator.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalConstructions.finite_hierarchy hℳ) (transitive_closure_operator_models hℳ))

private theorem finite_universe_operator_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.finite_universe_operator.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalConstructions.finite_universe hℳ) (finite_hierarchy_operator_models hℳ))

private theorem hereditarily_finite_predicate_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.hereditarily_finite_predicate.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalRelations.hereditarily_finite hℳ) (finite_universe_operator_models hℳ))

private theorem finite_subset_collection_separation_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.finite_subset_collection_separation.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalSeparation.finite_subset_collection hℳ) (hereditarily_finite_predicate_models hℳ))

private theorem finite_subset_collection_operator_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.finite_subset_collection_operator.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalConstructions.finite_subset_collection hℳ) (finite_subset_collection_separation_models hℳ))

private theorem hereditarily_finite_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.hereditarily_finite.theory :=
  (finite_subset_collection_operator_models hℳ)

private theorem finite_sequence_concatenation_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.finite_sequence_concatenation.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalConstructions.finite_sequence_concatenation hℳ) (hereditarily_finite_models hℳ))

private theorem nonempty_finite_sequence_space_separation_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.nonempty_finite_sequence_space_separation.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalSeparation.nonempty_sequence_space hℳ) (finite_sequence_concatenation_models hℳ))

private theorem nonempty_finite_sequence_space_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.nonempty_finite_sequence_space.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalConstructions.nonempty_finite_sequence_space hℳ) (nonempty_finite_sequence_space_separation_models hℳ))

private theorem finite_sequence_flatten_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.finite_sequence_flatten.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalConstructions.finite_sequence_flatten hℳ) (nonempty_finite_sequence_space_models hℳ))

private theorem finite_sequence_support_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.finite_sequence_support.theory :=
  (FiniteAxiomBasis.union_models (membership_irreflexive_models hℳ) (FiniteAxiomBasis.union_models (empty_set_symbol_models hℳ) (FiniteAxiomBasis.union_models (successor_operator_models hℳ) (FiniteAxiomBasis.union_models (binary_union_operator_models hℳ) (FiniteAxiomBasis.union_models (ordered_pair_operator_models hℳ) (FiniteAxiomBasis.union_models (function_application_models hℳ) (FiniteAxiomBasis.union_models (finite_sequence_flatten_models hℳ) (finite_sequence_space_models hℳ))))))))

private theorem intrinsic_arithmetic_evaluation_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.intrinsic_arithmetic_evaluation.theory :=
  (FiniteAxiomBasis.union_models (formal_language_encoding_models hℳ) (finite_sequence_support_models hℳ))

private theorem expression_encoding_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.expression_encoding.theory :=
  (FiniteAxiomBasis.union_models (membership_irreflexive_models hℳ) (FiniteAxiomBasis.union_models (FiniteAxiomBasis.insert_models (PureFinalSyntax.free_variable_occurs hℳ) (FiniteAxiomBasis.insert_models (PureFinalSyntax.syntax_transform hℳ) (formal_language_encoding_models hℳ))) (empty_set_symbol_models hℳ)))

private theorem propositional_axiom_schema_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.propositional_axiom_schema.theory :=
  (FiniteAxiomBasis.insert_models ((PureFinalSyntax.schema_axioms hℳ).1) (expression_encoding_models hℳ))

private theorem quantifier_axiom_schema_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.quantifier_axiom_schema.theory :=
  (FiniteAxiomBasis.insert_models ((PureFinalSyntax.schema_axioms hℳ).2.1) (propositional_axiom_schema_models hℳ))

private theorem equality_axiom_schema_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.equality_axiom_schema.theory :=
  (FiniteAxiomBasis.insert_models ((PureFinalSyntax.schema_axioms hℳ).2.2) (quantifier_axiom_schema_models hℳ))

private theorem logical_axiom_code_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.logical_axiom_code.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalSyntax.logical_axioms hℳ) (equality_axiom_schema_models hℳ))

private theorem logical_rule_encoding_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.logical_rule_encoding.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalSyntax.modus_ponens hℳ) (logical_axiom_code_models hℳ))

private theorem related_symbol_semantics_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.related_symbol_semantics.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalSyntax.nonlogical_symbols hℳ) (logical_rule_encoding_models hℳ))

private theorem related_syntax_semantics_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.related_syntax_semantics.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalSyntax.related_syntax hℳ) (related_symbol_semantics_models hℳ))

private theorem structure_semantics_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.structure_semantics.theory :=
  (FiniteAxiomBasis.insert_models (PureFinalSyntax.structure_axiom hℳ) (related_syntax_semantics_models hℳ))

private theorem term_value_semantics_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.term_value_semantics.theory :=
  (FiniteAxiomBasis.insert_models (And.intro (PureFinalSyntax.term_value hℳ) (PureFinalSyntax.term_list_value hℳ)) (structure_semantics_models hℳ))

private theorem semantic_interpretation_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.semantic_interpretation.theory :=
  (term_value_semantics_models hℳ)

private theorem intrinsic_syntax_carrier_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.intrinsic_syntax_carrier.theory :=
  (FiniteAxiomBasis.union_models (FiniteAxiomBasis.union_models (subset_models hℳ) (empty_set_symbol_models hℳ)) (semantic_interpretation_models hℳ))

private theorem intrinsic_proof_row_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.intrinsic_proof_row.theory :=
  (FiniteAxiomBasis.union_models (intrinsic_syntax_carrier_models hℳ) (finite_sequence_support_models hℳ))

private theorem intrinsic_proof_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model SupportAxiomBasis.intrinsic_proof.theory :=
  (FiniteAxiomBasis.union_models (intrinsic_arithmetic_evaluation_models hℳ) (intrinsic_proof_row_models hℳ))

/-- 任意裸 ZFC 模型的规范扩张满足全部原支撑公理及其无限参数族。 -/
theorem support_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model intrinsic_proof_theory :=
  (FiniteAxiomBasis.models_iff SupportAxiomBasis.intrinsic_proof (E hℳ).model).mp
    (intrinsic_proof_models hℳ)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSupportModels
