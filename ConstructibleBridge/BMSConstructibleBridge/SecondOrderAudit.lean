import BMSConstructibleBridge.SecondOrderPresentation
import BMSConstructibleBridge.PrimitiveCoding
import BMSConstructibleBridge.PureSecondOrder
import BMSConstructibleBridge.TreeChain
import BMSConstructibleBridge.GraphNaturals
import BMSConstructibleBridge.GraphClosure
import BMSConstructibleBridge.GraphCountability
import BMSConstructibleBridge.GraphDomain
import BMSConstructibleBridge.GraphInterpretation
import BMSConstructibleBridge.GraphSeparation
import BMSConstructibleBridge.SecondOrderPairing
import BMSConstructibleBridge.SecondOrderUnpairing
import BMSConstructibleBridge.SecondOrderDomain
import BMSConstructibleBridge.SecondOrderInterpretation
import BMSConstructibleBridge.SecondOrderAxioms
import BMSConstructibleBridge.SecondOrderSeparationAxiom
import BMSConstructibleBridge.SecondOrderInfinityAxiom
import BMSConstructibleBridge.SecondOrderUnion
import BMSConstructibleBridge.SecondOrderPairSet
import BMSConstructibleBridge.SecondOrderFoundation
import BMSConstructibleBridge.SecondOrderWeakSetTheory
import BMSConstructibleBridge.SecondOrderNaturalNumbers
import BMSConstructibleBridge.SecondOrderCountabilityAxiom
import BMSConstructibleBridge.SecondOrderTMC
import BMSConstructibleBridge.SecondOrderFiniteCode
import BMSConstructibleBridge.SecondOrderNumberHistoryTheorem
import BMSConstructibleBridge.SecondOrderSetIterationTheorem
import BMSConstructibleBridge.SecondOrderAssignmentSyntax
import BMSConstructibleBridge.SecondOrderFormulaCode
import BMSConstructibleBridge.SecondOrderRankedRecursionTheorem
import BMSConstructibleBridge.SecondOrderEvaluationFixedPoint
import BMSConstructibleBridge.SecondOrderEvaluationEquations
import BMSConstructibleBridge.SecondOrderSourceSatisfaction
import BMSConstructibleBridge.SecondOrderDefinableFamilyTheorem
import BMSConstructibleBridge.SecondOrderDefinableRespect
import BMSConstructibleBridge.SecondOrderSubsetCollection
import BMSConstructibleBridge.SecondOrderDefinableObjects
import BMSConstructibleBridge.SecondOrderMemberFamily
import BMSConstructibleBridge.SecondOrderSubsetExact
import BMSConstructibleBridge.SecondOrderMemberCollection
import BMSConstructibleBridge.SecondOrderArithmetic
import BMSConstructibleBridge.PrimitiveProgram
import YesMetaZFC.BMS.FinitePatternDescent
import YesMetaZFC.BMS.SeedExpansion
import Lean.Util.CollectAxioms

/-!
# 二阶目标呈现与有限模式下降的独立审计

本入口与实际可构造层证明隔离；若不慎导入旧语义路线，立即报错。
标准公理检查不能替代 `Z₂` 对象推导，亦不消去框架良基性等显式前提。
-/

open Lean in
run_cmd do
  let E ← getEnv
  let S := #[`BMSConstructibleBridge.ArithmeticPresentation,
    `BMSConstructibleBridge.SecondOrderPresentation,
    `BMSConstructibleBridge.PrimitiveCoding,
    `BMSConstructibleBridge.CountableReflection,
    `BMSConstructibleBridge.CodedReflection,
    `BMSConstructibleBridge.SeedReflection,
    `BMSConstructibleBridge.SecondOrderSyntax,
    `BMSConstructibleBridge.TreeTransfer,
    `BMSConstructibleBridge.Bisimulation,
    `BMSConstructibleBridge.TreeChain,
    `BMSConstructibleBridge.CountableGraph,
    `BMSConstructibleBridge.GraphNaturals,
    `BMSConstructibleBridge.GraphClosure,
    `BMSConstructibleBridge.GraphFunctions,
    `BMSConstructibleBridge.GraphCountability,
    `BMSConstructibleBridge.GraphSyntax,
    `BMSConstructibleBridge.GraphDomain,
    `BMSConstructibleBridge.GraphQuotient,
    `BMSConstructibleBridge.GraphTranslation,
    `BMSConstructibleBridge.GraphInterpretation,
    `BMSConstructibleBridge.GraphSeparation,
    `BMSConstructibleBridge.SecondOrderSubstitution,
    `BMSConstructibleBridge.SecondOrderModel,
    `BMSConstructibleBridge.SecondOrderNumbers,
    `BMSConstructibleBridge.SecondOrderOrder,
    `BMSConstructibleBridge.SecondOrderPairing,
    `BMSConstructibleBridge.SecondOrderMultiplication,
    `BMSConstructibleBridge.SecondOrderAlgebra,
    `BMSConstructibleBridge.SecondOrderPairingBounds,
    `BMSConstructibleBridge.SecondOrderUnpairing,
    `BMSConstructibleBridge.SecondOrderRelations,
    `BMSConstructibleBridge.SecondOrderFunctions,
    `BMSConstructibleBridge.SecondOrderDomain,
    `BMSConstructibleBridge.SecondOrderRelationOps,
    `BMSConstructibleBridge.SecondOrderBisimulation,
    `BMSConstructibleBridge.SecondOrderGraph,
    `BMSConstructibleBridge.SecondOrderQuotient,
    `BMSConstructibleBridge.SecondOrderInterpretation,
    `BMSConstructibleBridge.SecondOrderCompleteness,
    `BMSConstructibleBridge.SecondOrderAxioms,
    `BMSConstructibleBridge.SecondOrderGraft,
    `BMSConstructibleBridge.SecondOrderChainMaps,
    `BMSConstructibleBridge.SecondOrderGraftDomain,
    `BMSConstructibleBridge.SecondOrderGraftSemantics,
    `BMSConstructibleBridge.SecondOrderSeparation,
    `BMSConstructibleBridge.SecondOrderSeparationAxiom,
    `BMSConstructibleBridge.SecondOrderDomainClosure,
    `BMSConstructibleBridge.SecondOrderNaturalGraph,
    `BMSConstructibleBridge.SecondOrderInfinity,
    `BMSConstructibleBridge.SecondOrderInfinityAxiom,
    `BMSConstructibleBridge.SecondOrderUnion,
    `BMSConstructibleBridge.SecondOrderTaggedGraph,
    `BMSConstructibleBridge.SecondOrderTaggedDomain,
    `BMSConstructibleBridge.SecondOrderPairSet,
    `BMSConstructibleBridge.SecondOrderMinimum,
    `BMSConstructibleBridge.SecondOrderHistory,
    `BMSConstructibleBridge.SecondOrderIteration,
    `BMSConstructibleBridge.SecondOrderGraphMinimum,
    `BMSConstructibleBridge.SecondOrderFoundation,
    `BMSConstructibleBridge.SecondOrderTransitiveSuperset,
    `BMSConstructibleBridge.SecondOrderNaturalNumbers,
    `BMSConstructibleBridge.SecondOrderWeakSetTheory,
    `BMSConstructibleBridge.SecondOrderPairLayer,
    `BMSConstructibleBridge.SecondOrderPairObjects,
    `BMSConstructibleBridge.SecondOrderOrderedLayer,
    `BMSConstructibleBridge.SecondOrderRelationImage,
    `BMSConstructibleBridge.SecondOrderMixedImage,
    `BMSConstructibleBridge.SecondOrderEnumeration,
    `BMSConstructibleBridge.SecondOrderFunctionObjects,
    `BMSConstructibleBridge.SecondOrderCountability,
    `BMSConstructibleBridge.SecondOrderOmega,
    `BMSConstructibleBridge.SecondOrderObjectSyntax,
    `BMSConstructibleBridge.SecondOrderOmegaSyntax,
    `BMSConstructibleBridge.SecondOrderCountabilityAxiom,
    `BMSConstructibleBridge.SecondOrderRelationDecode,
    `BMSConstructibleBridge.SecondOrderNaturalSubsets,
    `BMSConstructibleBridge.SecondOrderRegularRelation,
    `BMSConstructibleBridge.SecondOrderCollapseGraph,
    `BMSConstructibleBridge.SecondOrderCollapseFunction,
    `BMSConstructibleBridge.SecondOrderMostowski,
    `BMSConstructibleBridge.SecondOrderRelationSyntax,
    `BMSConstructibleBridge.SecondOrderCollapseSyntax,
    `BMSConstructibleBridge.SecondOrderMostowskiAxiom,
    `BMSConstructibleBridge.SecondOrderTMC,
    `BMSConstructibleBridge.SecondOrderDivision,
    `BMSConstructibleBridge.SecondOrderPowers,
    `BMSConstructibleBridge.SecondOrderBinaryPowers,
    `BMSConstructibleBridge.SecondOrderDigit,
    `BMSConstructibleBridge.SecondOrderFiniteCode,
    `BMSConstructibleBridge.SecondOrderFiniteRange,
    `BMSConstructibleBridge.SecondOrderSequenceCode,
    `BMSConstructibleBridge.SecondOrderSequenceSyntax,
    `BMSConstructibleBridge.SecondOrderNumberHistory,
    `BMSConstructibleBridge.SecondOrderPowerSyntax,
    `BMSConstructibleBridge.SecondOrderNumberHistoryTheorem,
    `BMSConstructibleBridge.SecondOrderSections,
    `BMSConstructibleBridge.SecondOrderSetOperator,
    `BMSConstructibleBridge.SecondOrderSetHistory,
    `BMSConstructibleBridge.SecondOrderSetIteration,
    `BMSConstructibleBridge.SecondOrderSetIterationTheorem,
    `BMSConstructibleBridge.SecondOrderAssignment,
    `BMSConstructibleBridge.SecondOrderAssignmentSyntax,
    `BMSConstructibleBridge.SecondOrderFormulaCode,
    `BMSConstructibleBridge.SecondOrderInitialAgreement,
    `BMSConstructibleBridge.SecondOrderRankedStability,
    `BMSConstructibleBridge.SecondOrderRankedRecursion,
    `BMSConstructibleBridge.SecondOrderRankedRecursionTheorem,
    `BMSConstructibleBridge.SecondOrderRecursiveRelation,
    `BMSConstructibleBridge.SecondOrderEvaluationRule,
    `BMSConstructibleBridge.SecondOrderEvaluationFixedPoint,
    `BMSConstructibleBridge.SecondOrderAssignmentCongruence,
    `BMSConstructibleBridge.SecondOrderEvaluationCongruence,
    `BMSConstructibleBridge.SecondOrderEvaluationEquations,
    `BMSConstructibleBridge.SecondOrderFormulaCompilation,
    `BMSConstructibleBridge.SecondOrderSourceEnvironment,
    `BMSConstructibleBridge.SecondOrderEvaluationLogic,
    `BMSConstructibleBridge.SecondOrderSourceSatisfaction,
    `BMSConstructibleBridge.SecondOrderSourceAssignment,
    `BMSConstructibleBridge.SecondOrderDefinableFamily,
    `BMSConstructibleBridge.SecondOrderDefinableCoverage,
    `BMSConstructibleBridge.SecondOrderDefinableFamilyTheorem,
    `BMSConstructibleBridge.SecondOrderRelatedAssignments,
    `BMSConstructibleBridge.SecondOrderEvaluationRespect,
    `BMSConstructibleBridge.SecondOrderDefinableRespect,
    `BMSConstructibleBridge.SecondOrderSubsetLayer,
    `BMSConstructibleBridge.SecondOrderSubsetCollection,
    `BMSConstructibleBridge.SecondOrderMemberNormalizer,
    `BMSConstructibleBridge.SecondOrderMemberRelations,
    `BMSConstructibleBridge.SecondOrderMemberStructure,
    `BMSConstructibleBridge.SecondOrderDefinableObjects,
    `BMSConstructibleBridge.SecondOrderMemberFamily,
    `BMSConstructibleBridge.SecondOrderSubsetExact,
    `BMSConstructibleBridge.SecondOrderMemberCollection,
    `BMSConstructibleBridge.PrimitiveHistory,
    `BMSConstructibleBridge.PrimitiveFormulas,
    `BMSConstructibleBridge.PureSecondOrder,
    `BMSConstructibleBridge.SecondOrderArithmetic,
    `BMSConstructibleBridge.PrimitiveProgram,
    `YesMetaZFC.BMS.HeightDescent,
    `YesMetaZFC.BMS.FinitePatternDescent,
    `YesMetaZFC.BMS.SeedExpansion]
  for M in E.header.moduleNames do
    if (`ConstructibleUniverse).isPrefixOf M ||
        (`Mathlib.SetTheory.Ordinal).isPrefixOf M ||
        ((`BMSConstructibleBridge).isPrefixOf M && !S.contains M) then
      throwError "二阶呈现导入了被禁止的序数或桥接语义模块：{M}"
  let A := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut n : Nat := 0
  for (c, _) in E.constants.toList do
    if let some i := E.getModuleIdxFor? c then
      if S.contains E.header.moduleNames[i.toNat]! then
        let B ← collectAxioms c
        unless (B.filter (!A.contains ·)).isEmpty do
          throwError "{c} 存在非标准公理依赖：{B}"
        n := n + 1
  if n == 0 then
    throwError "没有检查任何二阶呈现声明"
  for c in #[``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPresentation.sentence_iff_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCountabilityAxiom.derives_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMostowskiAxiom.derives_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTMC.models_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTMC.derives_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDivision.unique_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPowers.exists_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPowers.add_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteCode.segment_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSequenceCode.exists_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderNumberHistoryTheorem.derives_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSetIteration.exists_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSetIterationTheorem.derives_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAssignment.prepend_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAssignmentSyntax.prepend_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFormulaCode.children_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRankedStability.stages_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRankedRecursion.exists_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRankedRecursionTheorem.pure_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRankedRecursionTheorem.derives_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAssignmentSyntax.extension_formula_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRecursiveRelation.exists_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationRule.formula_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationFixedPoint.exists_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationFixedPoint.derives_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAssignmentCongruence.extension_exists_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationCongruence.congr_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationEquations.equality_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationEquations.membership_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationEquations.negation_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationEquations.conjunction_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationEquations.existential_all_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFormulaCompilation.term_weaken_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSourceEnvironment.extend_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationLogic.universal_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSourceSatisfaction.formula_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSourceSatisfaction.closed_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSourceAssignment.model_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDefinableFamily.exists_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDefinableCoverage.exists_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDefinableFamilyTheorem.derives_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelatedAssignments.extension_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationRespect.respect_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDefinableRespect.slice_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSubsetLayer.wf_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSubsetLayer.mem_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSubsetCollection.family_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberNormalizer.code_mem_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberRelations.graphs_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberStructure.surjective_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberStructure.coverage_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDefinableObjects.exists_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberFamily.exists_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSubsetExact.mem_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberCollection.exists_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberCollection.coverage_l,
      ``YesMetaZFC.BMS.StabilityFrame.FinitePatternDescent.wellOrder_l,
      ``YesMetaZFC.BMS.HeightDescent.positive_iff_l,
      ``YesMetaZFC.BMS.HeightDescent.seed_one_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.PrimitiveCoding.trim_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.PrimitiveCoding.parent_zero_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.PrimitiveCoding.parent_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.PrimitiveCoding.expand_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.PrimitiveCoding.check_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.PrimitiveCoding.norm_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.CountableReflection.system_l.seed_acc_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.CodedReflection.principle_iff_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.CodedReflection.wellOrder_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.CodedReflection.sentence_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.CodedReflection.seed_acc_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SeedReflection.acc_iff_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SeedReflection.sentence_iff_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSyntax.closed_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSyntax.closed_pi11_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.TreeTransfer.pullback_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.Bisimulation.unfold_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.Bisimulation.coded_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.TreeChain.lift_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.TreeChain.no_chain_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.PrimitiveHistory.history_iff_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSyntax.beta_pure_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSyntax.beta_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.PrimitiveFormulas.primrec_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.PureSecondOrder.formula_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.PureSecondOrder.closed_formula_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.PureSecondOrder.closed_eq_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.CountableGraph.ext_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.CountableGraph.wellFounded_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.CountableGraph.sep_mem_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.CountableGraph.union_mem_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.CountableGraph.pair_mem_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.CountableGraph.enumerate_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.CountableGraph.lift_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.GraphNaturals.nat_eq_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.GraphNaturals.nat_lt_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.GraphNaturals.infinite_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.GraphClosure.closure_transitive_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.GraphClosure.collapse_transitive_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.GraphClosure.point_unique_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.GraphFunctions.ordered_eq_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.GraphFunctions.map_graph_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.GraphFunctions.map_unique_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.GraphFunctions.collapse_range_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.GraphCountability.countable_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.GraphSyntax.witness_pure_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.GraphSyntax.matrix_pure_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.GraphSyntax.mem_matrix_pure_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.GraphSyntax.eq_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.GraphSyntax.mem_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.GraphDomain.matrix_pure_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.GraphDomain.acc_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.GraphDomain.real_decode_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.GraphDomain.eq_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.GraphDomain.mem_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.GraphQuotient.eq_iff_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.GraphQuotient.wellFounded_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.GraphInterpretation.form_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.GraphInterpretation.congr_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSubstitution.form_subst_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.GraphTranslation.form_pure_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.GraphTranslation.comprehension_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.GraphTranslation.induction_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.GraphSeparation.mem_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.GraphSeparation.selector_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.GraphSeparation.comprehension_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderModel.comprehension_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderModel.induction_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderNumbers.add_cancel_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrder.trichotomy_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPairing.total_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPairing.edge_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderArithmetic.models_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderArithmetic.comprehension_derives_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderArithmetic.empty_derives_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderArithmetic.induction_derives_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderArithmetic.induction_rule_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderArithmetic.numeral_add_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderArithmetic.numeral_mul_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderArithmetic.zero_add_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderArithmetic.numeral_ne_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderArithmetic.eval_derives_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderUnion.derives_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTaggedGraph.exists_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTaggedDomain.wf_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPairSet.derives_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDomainClosure.iff_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderNaturalGraph.wf_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderInfinity.exists_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderInfinityAxiom.derives_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderGraft.exists_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderGraftDomain.shift_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderGraftDomain.root_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderGraftSemantics.eq_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderGraftSemantics.exists_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSeparation.exists_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSeparationAxiom.derives_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCompleteness.schedule_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAxioms.extensionality_derives_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAxioms.empty_derives_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAxioms.unpair_derives_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderBisimulation.maximum_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderBisimulation.unfold_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderBisimulation.mem_formula_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderGraph.mem_congr_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderGraph.ext_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderQuotient.ext_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderQuotient.empty_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderInterpretation.form_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderInterpretation.congr_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelations.comprehension_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelations.comprehension_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelations.ext_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFunctions.prefix_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFunctions.prefix_function_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDomain.formula_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDomain.child_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMultiplication.mul_assoc_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAlgebra.ordered_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAlgebra.lt_iff_add_one_le_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPairingBounds.injective_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderUnpairing.unique_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderUnpairing.left_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderUnpairing.right_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.PrimitiveProgram.graph_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.PrimitiveProgram.complete_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.PrimitiveProgram.sound_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.PrimitiveProgram.add_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.PrimitiveProgram.mul_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderArithmetic.consistent_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.ArithmeticPresentation.equiv_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPresentation.height_sentence_iff_l,
      ``YesMetaZFC.BMS.SeedExpansion.acc_l] do
    unless E.contains c do
      throwError "缺少本轮关键定理：{c}"
  logInfo m!"二阶呈现审计通过：{n} 个声明；无可构造语义或 Ordinal 导入；仅标准公理。"

#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPresentation.sentence_iff_l
#print axioms YesMetaZFC.BMS.StabilityFrame.FinitePatternDescent.wellOrder_l
#print axioms YesMetaZFC.BMS.HeightDescent.seed_one_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.PrimitiveCoding.parent_zero_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.PrimitiveCoding.check_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.PrimitiveCoding.norm_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.CodedReflection.wellOrder_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.CodedReflection.sentence_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SeedReflection.acc_iff_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSyntax.closed_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.TreeTransfer.pullback_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.Bisimulation.unfold_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.TreeChain.no_chain_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.PrimitiveHistory.history_iff_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.PrimitiveFormulas.primrec_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.PureSecondOrder.formula_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.PureSecondOrder.closed_formula_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.CountableGraph.ext_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.CountableGraph.wellFounded_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.CountableGraph.sep_mem_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.CountableGraph.lift_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.GraphNaturals.infinite_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.GraphClosure.point_unique_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.GraphFunctions.ordered_eq_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.GraphFunctions.collapse_range_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.GraphCountability.countable_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.GraphSyntax.eq_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.GraphSyntax.mem_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.GraphDomain.acc_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.GraphDomain.mem_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.GraphQuotient.wellFounded_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.GraphInterpretation.form_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSubstitution.form_subst_m
#print axioms YesMetaZFC.BMS.ConstructibleBridge.GraphTranslation.comprehension_m
#print axioms YesMetaZFC.BMS.ConstructibleBridge.GraphTranslation.induction_m
#print axioms YesMetaZFC.BMS.ConstructibleBridge.GraphSeparation.comprehension_m
#print axioms YesMetaZFC.BMS.ConstructibleBridge.GraphSeparation.mem_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderModel.induction_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderNumbers.add_cancel_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrder.trichotomy_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPairing.total_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAlgebra.ordered_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPairingBounds.injective_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderUnpairing.unique_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderUnpairing.left_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderUnpairing.right_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelations.comprehension_m
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelations.comprehension_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDomain.formula_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDomain.child_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderBisimulation.unfold_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderGraph.ext_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderQuotient.ext_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderInterpretation.form_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderInterpretation.congr_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAxioms.extensionality_derives_m
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAxioms.empty_derives_m
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAxioms.unpair_derives_m
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderGraftDomain.root_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderGraftSemantics.exists_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSeparation.exists_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSeparationAxiom.derives_m
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderNaturalGraph.wf_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderInfinityAxiom.derives_m
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderUnion.derives_m
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTaggedDomain.wf_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPairSet.derives_m
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMinimum.choice_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderHistory.exists_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderIteration.chain_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderGraphMinimum.exists_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFoundation.derives_m
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFoundation.irrefl_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTransitiveSuperset.derives_m
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderNaturalNumbers.eq_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderNaturalNumbers.least_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderWeakSetTheory.derives_m
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPairLayer.exists_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPairObjects.ordered_eq_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrderedLayer.formula_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelationImage.quotient_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMixedImage.exists_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEnumeration.eq_iff_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCountability.exists_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOmega.range_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderObjectSyntax.map_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCountabilityAxiom.derives_m
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelationDecode.exists_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRegularRelation.wf_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRegularRelation.field_iff_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCollapseGraph.graph_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCollapseFunction.exists_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMostowski.collapse_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMostowskiAxiom.derives_m
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTMC.derives_m
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTMC.consistency_m
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDivision.unique_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPowers.exists_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPowers.unique_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPowers.add_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderBinaryPowers.even_multiple_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDigit.periodic_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteCode.segment_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteRange.partial_bound_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSequenceCode.exists_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSequenceSyntax.decode_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderNumberHistory.exists_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderNumberHistoryTheorem.derives_m
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSections.extend_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSetHistory.exists_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSetIteration.exists_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSetIteration.unique_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSetIterationTheorem.derives_m
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAssignment.prepend_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAssignmentSyntax.prepend_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFormulaCode.children_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRankedStability.stages_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRankedRecursion.exists_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRankedRecursionTheorem.derives_m
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAssignmentSyntax.extension_formula_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRecursiveRelation.exists_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationRule.formula_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationFixedPoint.exists_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationFixedPoint.derives_m
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAssignmentCongruence.extension_exists_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationCongruence.congr_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationEquations.equality_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationEquations.membership_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationEquations.negation_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationEquations.conjunction_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationEquations.existential_all_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFormulaCompilation.term_weaken_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSourceEnvironment.extend_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationLogic.universal_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSourceSatisfaction.formula_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSourceSatisfaction.closed_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSourceAssignment.model_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDefinableFamily.exists_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDefinableCoverage.exists_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDefinableFamilyTheorem.derives_m
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelatedAssignments.extension_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationRespect.respect_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDefinableRespect.slice_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSubsetLayer.wf_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSubsetLayer.mem_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSubsetCollection.family_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberNormalizer.code_mem_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberRelations.graphs_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberStructure.surjective_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberStructure.coverage_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDefinableObjects.exists_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberFamily.exists_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSubsetExact.mem_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberCollection.exists_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberCollection.coverage_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderArithmetic.empty_derives_m
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderArithmetic.induction_derives_m
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderArithmetic.eval_derives_m
#print axioms YesMetaZFC.BMS.ConstructibleBridge.PrimitiveProgram.graph_m
#print axioms YesMetaZFC.BMS.ConstructibleBridge.PrimitiveProgram.mul_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderArithmetic.consistent_m
