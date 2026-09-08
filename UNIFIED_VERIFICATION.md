# 支撑理论统一验证

验证对象为原 `intrinsic_proof_theory` 及 `intrinsic_zfc_theory`，不是另外弱化后的公理集。指定纯 Rosser 的对应与裸 ZFC 独立性现也已完成，入口为 `PureRosser.agreement`、`PureRosser.independent`。

## 验证入口

- `PureSupportModels.support_models`：规范扩张满足整个原支撑理论。
- `PureZFCModels.models`：再加入全部原 ZFC 公理像，满足原 `intrinsic_zfc_theory`。
- `PureZFCModels.translated_models`：全部原公理的实际纯翻译在裸 ZFC 模型中成立。
- `PureZFCModels.expands`、`reduction`：模型扩张与任意原模型的纯约化。

## 范围与计数

119 条有限基公理由 108 个具体闭句和 11 类参数分离闭模板组成；项求值与项列求值的合取按原基计为一条。两个不同的普通分离闭句分别计数。
下表是原基结构的可读索引；覆盖性由 132 个组合节点和 `FiniteAxiomBasis.models_iff` 的 Lean 证明保证，而不是由文本计数推断。

模型内部的自然数、递归和分离均保留原含义，不假定模型在外部标准或良基。所有原 guard 保留。

## 本轮修正

1. 有序对反转原公理不带 guard。原纯图在非有序对输入上直接返回空集，不满足“交换两个投影并组成有序对”的要求；现直接组合已总化的左右投影与 Kuratowski 编码，任意输入的存在唯一性和原闭句均重新验证。
2. 原复合项为 `second ∘ first`。原成员图按执行顺序接收参数，函数槽却按书写顺序传入；现由 `relationComposition_order` 显式连接这两个顺序。源公理与 quotation 不变。

## 仍未声称完成的结论

- 原递归序列族之并在合法递归器下为 ω 上总函数的独立数学定理。其原定义公理本身已纳入本轮验证。

## Rosser 配置增量

初次配置阶段没有修改源签名、公理、原 Rosser 句子或 quotation；随后获准的自然数迁移见下节。

| 接口 | 已验证内容 |
| --- | --- |
| `SyntaxNatCoding.formula_coding` | 可数符号表上的内在良构语法单射编码 |
| `PureRosserSchedule.source`、`target` | 原支撑签名及纯签名的具体公平 Henkin 调度 |
| `PureRosser.sentence`、`comparison` | 最终解释下的两个实际纯隶属闭句 |
| `PureRosser.truth_iff` | 纯句子与规范扩张中的当前源句子真值一致 |
| `PureRosser.translate_derives` | 任意源闭句推导向裸 ZFC 推导的正向传输 |
| `PureRosser.fixed_point` | 裸 ZFC 实际推导 `sentence ↔ ¬ comparison` |
| `PureRosser.agreement_iff_comparison` | 任意原模型上的句子对应与比较式对应严格等价 |
| `PureRosser.source_consistent` | 裸 ZFC 一致性推出原支撑理论一致性 |
| `PureRosser.independent_of_agreement` | 句子和调度已固定，仍显式要求 `Agreement` 的条件独立性接口 |

比较式消费源证明树和源 quotation，并非纯语言自身 quotation 的另一次对角化。
`Agreement` 不是新公理；它现已由 `PureRosser.agreement` 证明。

## Agreement 基础对应与原码域边界

| 接口 | 已验证内容 |
| --- | --- |
| `PureSourceNumerals.empty_agrees`、`successor_agrees` | 任意原模型与其规范重扩张的空集、任意输入后继取值一致 |
| `PureSourceNumerals.numeral_agrees`、`quotation_agrees` | 全部标准 numeral 及当前 quotation 的值一致 |
| `PureSourceNumerals.proof_numeral_agrees` | 全部标准证明码实例在两模型中真值一致 |
| `RosserDomainBoundary.domain_agrees` | 后继码域条件在两模型中真值一致 |
| `RosserDomainBoundary.domain_not_subset_naturals` | 任意原模型中，ω 满足码域条件且 ω 不属于 ω |
| `RosserDomainBoundary.pairing_instance_vacuous` | 非自然数首参数使原配数定义实例因 guard 为假而成立 |
| `NaturalProofPresentation.presentation`、`ReducedNaturalProofPresentation.presentation` | 保留检查器、完备性及标准码正负表示，要求证明码属于内部 ω 的完整表示；现已接入 Rosser |

标准 numeral 的外部归纳只证明标准码实例；不能把模型内部的全部自然数当作这些 numeral。
后继码域又包含内部自然数集合之外的对象。完整证明图的根项为
`IntrinsicQuotation.node 1 [code, conclusion]`，轨迹只保证这个根项属于 ω。
原配数公理的自然数 guard 不能仅由该结论或码域条件取得。

这些基础事实本身不足以得到 `Agreement`；后续内部自然数图与实际局部行的对应已完成此证明。
以上边界证明没有构造整个原理论的反模型，也没有证明 `Agreement` 为假或不可证明。

用户批准后，具体包装已迁至 `ReducedNaturalProofPresentation`，并接入
`ReducedRosser.presentation` 的 `proof` 与 `assembly`。源固定点及其 quotation 已重新生成，
纯翻译、源固定点、原理论独立性与纯固定点均重新构建通过。
源签名、公理和 quotation 编码规则没有修改；新 `code ∈ ω` guard 排除了此前的非自然数输入问题。

## 当前自然数迁移及 Agreement 接口

| 接口 | 已验证内容 |
| --- | --- |
| `ReducedNaturalProofPresentation.natural_of_satisfied` | 任意接受的证明码都属于模型内部 ω |
| `PureSourceInfinity.inductive_agrees` | 原归纳集谓词与规范重扩张一致 |
| `PureSourceInfinity.omega_agrees` | 由原归纳核方程和最小性，确定两模型有同一个内部 ω |
| `PureSourceInfinity.member_natural`、`natural_compare` | 内部自然数的元素闭性及三歧性 |
| `RosserDomainBoundary.natural_in_domain` | 每个内部自然数满足旧后继码域 |
| `NaturalRosserSemantics.natural_comparison_satisfies` | 通用自然数包装的比较式精确语义 |
| `PureNaturalRosserAgreement.comparison_naturals` | 实际比较式等价于内部自然数见证及其初始段上的原对象证明图 |
| `PureNaturalRosserAgreement.agreement_of_natural_proofs` | 当前句子及其否定的两项 `ProofAgreement` 足以得到实际 `PureRosser.Agreement` |

充分条件 `ProofAgreement h𝒩 φ` 精确要求：对任意原模型 `𝒩` 的每个 `p ∈ ω`，
原完整证明图在 `𝒩` 与其规范重扩张中对结论 `φ` 真值一致。
需要的两个结论为当前 Rosser 句子及其否定；现均由 `PureSourceLocalTests.proof_agreement` 提供。
内部自然数可以非标准；实际局部行对应填满充分条件后，`PureRosser.agreement` 与 `independent` 得到无缺口的终局。

## 支撑语言 Δ₀ 分类及轨迹归约

| 接口 | 已验证内容 |
| --- | --- |
| `NaturalProofPresentation.comparison_delta0` | 原自然数 guard 使实际外层存在量词有界 |
| `ReducedRosser.predicate_delta0` | 任意结论的当前 Rosser 比较式在支撑语言中为 Δ₀ |
| `ReducedRosser.delta0Sentence_delta0`、`delta0Sentence_independent` | 比较式否定为 Δ₀；通过既有 `fixed_point` 等价，原理论一致性推出其两侧不可证 |
| `PureSourceBounds.power_agrees`、`trace_bound_agrees` | 任意原模型的全部幂集值及实际轨迹界 `P(ω)` 保持 |
| `PureSourceBounds.trace_row_natural` | 候选轨迹中的全部行属于模型内部 ω |
| `ReducedProofPresentation.graph_condition`、`PureNaturalRosserAgreement.proof_trace` | 实际完整证明图等于具体行模板的有界轨迹语义 |
| `PureNaturalRosserAgreement.proof_agreement_of_rows` | 根值对应已自动提供，只需候选轨迹内局部行对应即可得到自然数证明图对应 |

本轮新增 Δ₀ 代表，没有重新改变当前源固定点、公理或 quotation。
分类使用含 ω、幂集及编码函数的支撑语言，不声称实际纯隶属翻译或一阶算术语言中的 Δ₀。
纯关系式翻译的输出见证界仍需单独核验；相对 Δ₀ 绝对性不能免除函数解释对应义务。
内部算术/编码及具体局部行对应均已完成，两个 `ProofAgreement` 与最终 `Agreement` 已填入（见文末增量）。

## 纯语言 Δ₀ 的核验结论

当前无参数纯闭句的正向 Δ₀ 分类不是待补齐定理。纯签名没有函数、常元或零元关系，
通用 `FunctionFreeDelta0.closed_decided` 已证明其闭 Δ₀ 公式均能由纯逻辑决定。
当前两个翻译闭句的最外层存在量词还直接给出了无条件的否定分类。

| 接口 | 已验证内容 |
| --- | --- |
| `PureRosserDelta0.sentence_not_delta0`、`comparison_not_delta0` | 当前纯固定点和比较式的语法分类均不是 Δ₀ |
| `PureRosserDelta0.no_closed_delta0_equivalent` | 仅假定裸 ZFC 一致，任何 ZFC 可证明等价的无参数闭句也不能是 Δ₀ |
| `PureRosserDelta0.matrix_delta0` | `δ(w,A,B) := ¬∃p∈w (p∈A ∧ ∀q∈p q∉B)` 只含纯 ∈，确为 Δ₀ |
| `PureRosserDelta0.proofCondition_correct` | 证明码集合使用原完整图的实际纯翻译 |
| `PureRosserDelta0.parameters_exists`、`parameters_unique` | 裸 ZFC 模型中存在唯一的内部 ω 与两侧自然数证明码集合 |
| `PureRosserDelta0.sentence_iff_matrix` | 指定这些实际参数后，矩阵与当前纯 Rosser 句子真值一致 |
| `PureRosserDelta0.representation_derives` | 实际普通推导 `ZFC ⊢ R ↔ ∃w,A,B (Def(w,A,B) ∧ δ(w,A,B))` |
| `PureRosserDelta0.representation_not_delta0` | 保留参数定义的完整存在闭句非 Δ₀ |

参数定义 `Def` 使用纯分离所需的实际证明正文；其复杂度没有降为 Δ₀，也没有给出
原证明谓词的纯 Δ₀ 定义。上述正向存在、唯一性和推导等价均不要求 `Agreement`；
它们只使用规范扩张，不能填入任意原模型的 `Agreement`。源句子和 quotation 未修改。

## 公理与证明索引

| 编号 | 原基公理或模板 | 验证定理 |
| --- | --- | --- |
| 1 | `(empty_predicate (free := [])).separation_axiom` | `PureSupportSeparation.separation_axiom (empty_predicate (free := []))` |
| 2 | `membership_relation_predicate.separation_axiom` | `PureSupportSeparation.separation_axiom membership_relation_predicate` |
| 3 | `Nonlogical.BasicSetTheory.infinity_axiom` | `PureFinalInfinity.infinity` |
| 4 | `term_value_definition_axiom ∧ₘ term_list_value_definition_axiom` | `And.intro (PureFinalSyntax.term_value) (PureFinalSyntax.term_list_value)` |
| 5 | `binary_union_definition_axiom` | `PureFinalBasic.binary_union` |
| 6 | `bounded_subset_definition_axiom` | `PureFinalRelations.bounded_subset` |
| 7 | `cardinality_leq_definition_axiom` | `PureFinalRelations.cardinality_leq` |
| 8 | `cardinality_strict_less_definition_axiom` | `PureFinalRelations.cardinality_strict_less` |
| 9 | `cartesian_product_definition_axiom` | `PureFinalCollections.cartesian_product` |
| 10 | `domain_definition_axiom` | `PureFinalMappings.domain` |
| 11 | `empty_set_definition_axiom` | `PureFinalBasic.empty_set` |
| 12 | `equality_axiom_schema_definition_axiom` | `(PureFinalSyntax.schema_axioms).2.2` |
| 13 | `extensionality_axiom` | `PureFinalBasic.extensionality_axiom` |
| 14 | `finite_hierarchy_definition_axiom` | `PureFinalConstructions.finite_hierarchy` |
| 15 | `finite_sequence_concatenation_definition_axiom` | `PureFinalConstructions.finite_sequence_concatenation` |
| 16 | `finite_sequence_flatten_definition_axiom` | `PureFinalConstructions.finite_sequence_flatten` |
| 17 | `finite_sequence_space_definition_axiom` | `PureFinalConstructions.finite_sequence_space` |
| 18 | `finite_subset_collection_definition_axiom` | `PureFinalConstructions.finite_subset_collection` |
| 19 | `finite_subset_collection_separation_axiom` | `PureFinalSeparation.finite_subset_collection` |
| 20 | `finite_universe_definition_axiom` | `PureFinalConstructions.finite_universe` |
| 21 | `free_variable_occurs_definition_axiom` | `PureFinalSyntax.free_variable_occurs` |
| 22 | `function_application_definition_axiom` | `PureFinalMappings.application` |
| 23 | `godel_pairing_definition_axiom` | `PureFinalConstructions.godel_pairing` |
| 24 | `hereditarily_finite_definition_axiom` | `PureFinalRelations.hereditarily_finite` |
| 25 | `identity_definition_axiom` | `PureFinalCollections.identity` |
| 26 | `image_definition_axiom` | `PureFinalOperations.image` |
| 27 | `index_order_definition_axiom` | `PureFinalConstructions.index_order` |
| 28 | `inductive_core_definition_axiom` | `PureFinalInfinity.inductive_core` |
| 29 | `is_bijection_definition_axiom` | `PureFinalRelations.is_bijection` |
| 30 | `is_countable_definition_axiom` | `PureFinalRelations.is_countable` |
| 31 | `is_countably_infinite_definition_axiom` | `PureFinalRelations.is_countably_infinite` |
| 32 | `is_dedekind_finite_definition_axiom` | `PureFinalRelations.is_dedekind_finite` |
| 33 | `is_equinumerous_definition_axiom` | `PureFinalRelations.is_equinumerous` |
| 34 | `is_equivalence_relation_definition_axiom` | `PureFinalRelations.is_equivalence_relation` |
| 35 | `is_finite_definition_axiom` | `PureFinalRelations.is_finite` |
| 36 | `is_function_definition_axiom` | `PureFinalMappings.is_function` |
| 37 | `is_inductive_set_definition_axiom` | `PureFinalRelations.is_inductive_set` |
| 38 | `is_infinite_definition_axiom` | `PureFinalRelations.is_infinite` |
| 39 | `is_injective_definition_axiom` | `PureFinalRelations.is_injective` |
| 40 | `is_linear_order_definition_axiom` | `PureFinalRelations.is_linear_order` |
| 41 | `is_mapping_definition_axiom` | `PureFinalMappings.is_mapping` |
| 42 | `is_natural_discrete_linear_order_definition_axiom` | `PureFinalRelations.is_natural_discrete_linear_order` |
| 43 | `is_order_embeddable_definition_axiom` | `PureFinalRelations.is_order_embeddable` |
| 44 | `is_order_embedding_definition_axiom` | `PureFinalRelations.is_order_embedding` |
| 45 | `is_order_isomorphic_definition_axiom` | `PureFinalRelations.is_order_isomorphic` |
| 46 | `is_order_isomorphism_definition_axiom` | `PureFinalRelations.is_order_isomorphism` |
| 47 | `is_ordered_pair_definition_axiom` | `PureFinalPairs.is_ordered_pair` |
| 48 | `is_relation_definition_axiom` | `PureFinalPairs.is_relation` |
| 49 | `is_surjective_definition_axiom` | `PureFinalRelations.is_surjective` |
| 50 | `is_transitive_set_definition_axiom` | `PureFinalRelations.is_transitive_set` |
| 51 | `is_uncountable_definition_axiom` | `PureFinalRelations.is_uncountable` |
| 52 | `left_projection_definition_axiom` | `PureFinalPairs.left_projection` |
| 53 | `logical_axiom_code_definition_axiom` | `PureFinalSyntax.logical_axioms` |
| 54 | `mapping_collection_definition_axiom` | `PureFinalCollections.mapping_collection` |
| 55 | `maximum_natural_order_definition_axiom` | `PureFinalExtrema.maximum_natural_order` |
| 56 | `membership_irreflexive_axiom` | `PureFinalBasic.irreflexivity` |
| 57 | `membership_relation_definition_axiom` | `PureFinalOperations.membership_relation` |
| 58 | `minimum_difference_definition_axiom` | `PureFinalConstructions.minimum_difference` |
| 59 | `minimum_linear_order_definition_axiom` | `PureFinalExtrema.minimum_linear_order` |
| 60 | `minimum_natural_order_definition_axiom` | `PureFinalExtrema.minimum_natural_order` |
| 61 | `modus_ponens_definition_axiom` | `PureFinalSyntax.modus_ponens` |
| 62 | `natural_addition_definition_axiom` | `PureFinalConstructions.natural_addition` |
| 63 | `natural_addition_upper_bound_axiom` | `PureFinalArithmetic.addition_upper_axiom` |
| 64 | `natural_difference_definition_axiom` | `PureFinalConstructions.natural_difference` |
| 65 | `natural_exponent_product_index_bound_axiom` | `PureFinalArithmetic.exponent_product_axiom` |
| 66 | `natural_exponentiation_definition_axiom` | `PureFinalConstructions.natural_exponentiation` |
| 67 | `natural_exponentiation_index_bound_axiom` | `PureFinalArithmetic.exponent_axiom` |
| 68 | `natural_godel_pairing_coordinate_bound_axiom` | `PureFinalArithmetic.pairing_axiom` |
| 69 | `natural_le_lt_transitivity_axiom` | `PureFinalArithmetic.transitivity_axiom` |
| 70 | `natural_multiplication_definition_axiom` | `PureFinalConstructions.natural_multiplication` |
| 71 | `natural_order_type_definition_axiom` | `PureFinalConstructions.natural_order_type` |
| 72 | `natural_positive_left_addition_strict_bound_axiom` | `PureFinalArithmetic.positive_addition_axiom` |
| 73 | `natural_subset_type_definition_axiom` | `PureFinalConstructions.natural_subset_type` |
| 74 | `nonempty_finite_sequence_space_definition_axiom` | `PureFinalConstructions.nonempty_finite_sequence_space` |
| 75 | `nonempty_finite_sequence_space_separation_axiom` | `PureFinalSeparation.nonempty_sequence_space` |
| 76 | `omega_definition_axiom` | `PureFinalInfinity.omega` |
| 77 | `omega_pair_less_definition_axiom` | `PureFinalRelations.omega_pair_less` |
| 78 | `omega_recursive_sequence_definition_axiom` | `PureFinalConstructions.omega_recursive_sequence` |
| 79 | `ordered_pair_definition_axiom` | `PureFinalPairs.ordered_pair` |
| 80 | `ordered_pair_reverse_definition_axiom` | `PureFinalPairs.reverse` |
| 81 | `pair_definition_axiom` | `PureFinalBasic.pairing` |
| 82 | `pairing_axiom` | `PureFinalBasic.pairing_exists` |
| 83 | `power_set_axiom` | `PureFinalBasic.power_exists_axiom` |
| 84 | `power_set_bijection_definition_axiom` | `PureFinalConstructions.power_set_bijection` |
| 85 | `power_set_definition_axiom` | `PureFinalBasic.power_definition` |
| 86 | `propositional_axiom_schema_definition_axiom` | `(PureFinalSyntax.schema_axioms).1` |
| 87 | `quantifier_axiom_schema_definition_axiom` | `(PureFinalSyntax.schema_axioms).2.1` |
| 88 | `range_definition_axiom` | `PureFinalMappings.range` |
| 89 | `recursive_sequence_space_definition_axiom` | `PureFinalConstructions.recursive_sequence_space` |
| 90 | `related_nonlogical_symbol_set_definition_axiom` | `PureFinalSyntax.nonlogical_symbols` |
| 91 | `related_syntax_definition_axiom` | `PureFinalSyntax.related_syntax` |
| 92 | `relation_composition_definition_axiom` | `PureFinalOperations.composition` |
| 93 | `relation_converse_definition_axiom` | `PureFinalOperations.converse` |
| 94 | `relation_image_separation_axiom` | `PureFinalSeparation.relation_image` |
| 95 | `restriction_definition_axiom` | `PureFinalCollections.restriction` |
| 96 | `right_projection_definition_axiom` | `PureFinalPairs.right_projection` |
| 97 | `singleton_definition_axiom` | `PureFinalBasic.singleton` |
| 98 | `structural_syntax_definition_axiom` | `PureFinalSyntax.structural_syntax` |
| 99 | `structure_definition_axiom` | `PureFinalSyntax.structure_axiom` |
| 100 | `subset_definition_axiom` | `PureFinalBasic.subset` |
| 101 | `successor_definition_axiom` | `PureFinalBasic.successor` |
| 102 | `symmetric_difference_definition_axiom` | `PureFinalOperations.symmetric_difference` |
| 103 | `syntax_transform_definition_axiom` | `PureFinalSyntax.syntax_transform` |
| 104 | `transitive_closure_definition_axiom` | `PureFinalConstructions.transitive_closure` |
| 105 | `unbounded_subset_definition_axiom` | `PureFinalRelations.unbounded_subset` |
| 106 | `union_axiom` | `PureFinalBasic.union_exists_axiom` |
| 107 | `union_definition_axiom` | `PureFinalBasic.union_definition` |
| 108 | `well_order_definition_axiom` | `PureFinalRelations.well_order` |
| 109 | `SupportAssembly.closedTemplate .cartesianProduct` | `PureSupportSeparation.parameter_template` |
| 110 | `SupportAssembly.closedTemplate .composition` | `PureSupportSeparation.parameter_template` |
| 111 | `SupportAssembly.closedTemplate .converse` | `PureSupportSeparation.parameter_template` |
| 112 | `SupportAssembly.closedTemplate .domain` | `PureSupportSeparation.parameter_template` |
| 113 | `SupportAssembly.closedTemplate .identity` | `PureSupportSeparation.parameter_template` |
| 114 | `SupportAssembly.closedTemplate .indexOrder` | `PureSupportSeparation.parameter_template` |
| 115 | `SupportAssembly.closedTemplate .inductiveCore` | `PureSupportSeparation.parameter_template` |
| 116 | `SupportAssembly.closedTemplate .mappingCollection` | `PureSupportSeparation.parameter_template` |
| 117 | `SupportAssembly.closedTemplate .powerSetBijection` | `PureSupportSeparation.parameter_template` |
| 118 | `SupportAssembly.closedTemplate .range` | `PureSupportSeparation.parameter_template` |
| 119 | `SupportAssembly.closedTemplate .symmetricDifference` | `PureSupportSeparation.parameter_template` |

## 构建证据

- Lean 4.33.1；基线默认构建通过 752 个任务。
- 本轮全部新模块已进入默认导入图；最终 `lake --wfail build` 通过 **773 个任务，0 错误，0 警告**。
- 对四个汇总定理运行 Lean `#print axioms`，均不依赖 `sorryAx`。本轮 25 个新增或修改的 Lean 文件未声明新的自定义 `axiom`，也无 `sorry`、`admit` 或 `unsafe`。
- 可信依赖包含 Lean 既有的 `propext`、`Classical.choice`、`Quot.sound`（约化定理不使用 choice），以及项目原有 `SetTheory` 文件的原生计算证明。该结果不声称只依赖三个基础公理；原生计算也属于本项目既定可信基。
- 既有 `IntrinsicQuineCarrier` 的局部 simp 跟踪会在构建日志中重放信息；它不是警告或验证失败。


### 汇总定理可信依赖数量

| 定理 | 依赖数 | 其中项目既有原生计算项 |
| --- | --- | --- |
| `support_models` | 31 | 28 |
| `models` | 31 | 28 |
| `translated_models` | 31 | 28 |
| `reduct_models` | 9 | 7 |

原生计算项来自既有空集、外延性、基础、无穷、配对、幂集、并集公理闭性证书，
以及序数分类、序列限制和长度分类的 `prove_auto` 原生证书。未改动这些文件。


## Rosser 配置构建证据

- 三个新增模块和默认入口修改均已验证，`lake --wfail build` 成功通过 **776 个任务，0 错误，0 警告**。
- 使用公式参数上的 `translate_fixed_point` 再实例化，避免 Lean 在具体大 quotation 上进行全量定义转换；没有修改内核透明性规则或引入新公理。
- 源码只保留正式定义及证明，不含诊断副本、构建日志或样本测试。

- 对语法编码、两套公平调度、纯固定点、对应归约及条件独立性接口运行 `#print axioms`，均无 `sorryAx`。
  编码及调度各依赖 3 个 Lean 基础公理；后三项各有 32 项可信依赖，其中 29 项为项目既有原生计算证明。
  本次 4 个新增或修改的 Lean 文件没有 `sorry`、`admit`、`unsafe` 或新声明的自定义公理。

## Agreement 推进构建证据

- 三个新模块及默认导入已进入 `lake --wfail build`，共 **779 个任务，0 错误，0 警告**。
- 对标准码正负表示先证明通用模型真值定理，再实例化到实际完整证明图；避免内核展开巨大具体公式。
- 本轮新增或修改的四个 Lean 文件没有 `sorry`、`admit`、`unsafe` 或新声明的自定义公理。
- 下列 `#print axioms` 审计均无 `sorryAx`；原生依赖全部来自项目既有证明，未添加新的原生证书。

| 接口 | 总可信依赖 | 其中既有原生依赖 |
| --- | --- | --- |
| `NaturalProofPresentation.models_agree` | 3 | 0 |
| `NaturalProofPresentation.presentation` | 2 | 0 |
| `PureSourceNumerals.quotation_agrees` | 31 | 28 |
| `PureSourceNumerals.proof_numeral_agrees` | 32 | 29 |
| `RosserDomainBoundary.domain_agrees` | 31 | 28 |
| `RosserDomainBoundary.domain_not_subset_naturals` | 10 | 7 |
| `RosserDomainBoundary.pairing_instance_vacuous` | 0 | 0 |
| 自然数完整表示候选（现迁至 `ReducedNaturalProofPresentation`） | 11 | 8 |

源码包仅包含正式源码及文档；审计临时入口、日志、运行时和构建缓存不进入源码包。

## 内部自然数迁移构建证据

- 四个新增模块与五个已有 Lean 文件修改进入默认完整构建，`lake --wfail build` 通过 **783 个任务，0 错误，0 警告**。
- 以下实际迁移后定理经过 `#print axioms` 审计，均无 `sorryAx`；没有新声明的自定义公理或原生计算证书。
- 可信依赖沿用项目既定基础，内部 ω 的证明使用原归纳核方程与模型内部 ZF 定理。

| 接口 | 总可信依赖 | 其中既有原生依赖 |
| --- | --- | --- |
| `ReducedNaturalProofPresentation.natural_of_satisfied` | 11 | 8 |
| `ReducedRosser.fixed_point`、`independent` | 各 11 | 各 8 |
| `PureRosser.fixed_point` | 32 | 29 |
| `PureSourceInfinity.omega_agrees`、`member_natural` | 各 31 | 各 28 |
| `RosserDomainBoundary.natural_in_domain` | 31 | 28 |
| `NaturalRosserSemantics.natural_comparison_satisfies` | 2 | 0 |
| `PureNaturalRosserAgreement.comparison_naturals`、`agreement_of_natural_proofs` | 各 32 | 各 29 |

## Δ₀ 与轨迹对应构建证据

- 两个新增模块与四个已有 Lean 文件修改进入默认完整构建，`lake --wfail build` 通过 **785 个任务，0 错误，0 警告**。
- 15 个新增及终局接口的 `#print axioms` 审计均无 `sorryAx`。未新增 `axiom`、`sorry`、`admit`、`unsafe` 或原生计算证书；源码不包含临时审计入口和日志。
- 原源固定点及不可证性依赖仍为 11 项/8 项原生；纯固定点及最终条件接口仍为 32 项/29 项原生。

| 接口 | 总可信依赖 | 其中既有原生依赖 |
| --- | --- | --- |
| `NaturalProofPresentation.comparison_delta0` | 2 | 0 |
| `ReducedRosser.predicate_delta0`、`delta0Sentence_delta0`、`delta0Sentence_independent` | 各 11 | 各 8 |
| `ReducedProofPresentation.graph_condition` | 11 | 8 |
| `ObjectTrace.condition_satisfies` | 2 | 0 |
| `PureSourceBounds.power_agrees`、`trace_bound_agrees`、`trace_agrees` | 各 31 | 各 28 |
| `PureNaturalRosserAgreement.proof_trace` | 11 | 8 |
| `PureNaturalRosserAgreement.proof_agreement_of_rows` | 32 | 29 |

## 纯 Δ₀ 核验与参数矩阵构建证据

- 两个新增模块及三个已有 Lean 文件修改进入默认完整构建；`lake --wfail build` 通过 **787 个任务，0 错误，0 警告**。
- 18 个新接口及条件终局的 `#print axioms` 审计均无 `sorryAx`；原生依赖集合没有增加。未新增自定义 `axiom`、`sorry`、`admit`、`unsafe` 或原生计算证书。
- 通用无函数闭项排除和存在量词排除不依赖公理；通用闭句决定定理有 2 项 Lean 基础依赖、无原生依赖。具体定理类型中引用源图和 ZFC 理论会携带其既有定义证书，不代表添加了新的对象公理。

| 接口 | 总可信依赖 | 其中既有原生依赖 |
| --- | --- | --- |
| `FunctionFreeDelta0.no_closed_term`、`exists_not_delta0` | 各 0 | 各 0 |
| `FunctionFreeDelta0.closed_decided` | 2 | 0 |
| `ReducedRosser.predicate_exists_body`、`sentence_exists_body` | 各 11 | 各 8 |
| `PureRosserDelta0.closed_decided` | 9 | 7 |
| `PureRosserDelta0.sentence_not_delta0`、`comparison_not_delta0` | 各 11 | 各 8 |
| `PureRosserDelta0.no_closed_delta0_equivalent` | 32 | 29 |
| `PureRosserDelta0.matrix_delta0` | 0 | 0 |
| `PureRosserDelta0.proofCondition_correct`、`parameters_exists`、`parameters_unique` | 各 32 | 各 29 |
| `PureRosserDelta0.matrix_correct`、`sentence_iff_matrix`、`representation_derives` | 各 32 | 各 29 |
| `PureRosserDelta0.representation_not_delta0` | 11 | 8 |
| `PureRosser.independent_of_agreement` | 32 | 29 |


## 内部算术及根编码对应增量

- 三个新增模块与一个已有 Lean 模块修改进入默认构建；`lake --wfail build` 通过 **790 个任务，0 错误，0 警告**。
- 任意原模型的合法映射、定义域内应用以及内部自然数上的加、乘、幂、Gödel 配数、字段列和节点编码已对应到规范重扩张。根码使用当前实际 `IntrinsicQuotation.node 1 [code, quote(formula)]`，没有改变源句子或 quotation。
- 有限递推唯一性来自纯约化中的实际集合函数图。允许非标准内部长度，不用模型 ω 的外部良基性，也不对任意外部性质声称内部归纳。
- `root_agrees` 已消去 `proof_agreement_of_rows` 的根值前提；该接口现在仅要求候选轨迹中的实际局部行对应。该阶段留下的 `ProofAgreement`、`Agreement` 与最终裸 ZFC 独立性现已完成。
- 20 个接口的 `#print axioms` 审计全部无 `sorryAx`，依赖集合没有增加；未引入自定义公理、未完成证明、`unsafe` 或原生计算证书。

| 接口 | 总可信依赖 | 其中既有原生依赖 |
| --- | --- | --- |
| `PureSourceMappings.ordered_code` | 10 | 7 |
| `PureSourceMappings.ordered_agrees`、`function_predicate`、`mapping_project`、`application_agrees` | 各 31 | 各 28 |
| `PureSourceArithmetic.specification` | 10 | 7 |
| `PureSourceArithmetic.iteration_project`、`arithmetic_agrees_of_step` | 各 31 | 各 28 |
| `PureSourceArithmetic.addition_agrees`、`multiplication_agrees`、`exponentiation_agrees` | 各 31 | 各 28 |
| `PureSourceCoding.pairing_agrees`、`fields_agrees`、`node_agrees` | 各 31 | 各 28 |
| `PureSourceCoding.fields_natural`、`quotation_natural` | 各 10 | 各 7 |
| `PureNaturalRosserAgreement.root_natural` | 10 | 7 |
| `PureNaturalRosserAgreement.root_agrees` | 31 | 28 |
| `PureNaturalRosserAgreement.proof_agreement_of_rows`、`PureRosser.independent_of_agreement` | 各 32 | 各 29 |


## 实际局部行与裸 ZFC 独立性终局验证

- 六个新模块、三个既有 Lean 模块修改进入默认导入图，`lake --wfail build` 通过 **796 个任务，0 错误，0 警告**。
- `PureSourceSchemas.axiomTest` 保持实际有限公理表及三类模式连接的真值；每层有界量词的原界项在内部 ω 中取值。没有新增对象公理或标准性假设。
- `PureSourceLocalTests.row_agrees` 比较任意内部自然数行及任意集合轨迹；`proof_agreement` 对任意固定结论成立。
- `PureRosser.agreement` 填满实际合同，`PureRosser.independent` 仅要求裸 ZFC 一致性。当前句子、源 quotation 与纯 Δ₀ 三参数矩阵保持不变。
- 20 个新接口及终局接口经过 `#print axioms` 审计，无 `sorryAx`，对比上一稳定基点的依赖集合没有新增成员。源码没有新 `sorry`、`admit`、自定义 `axiom`、`unsafe` 或原生计算证书；临时审计代码和日志不入源码包。

| 接口 | 总可信依赖 | 其中既有原生依赖 |
| --- | --- | --- |
| `ObjectHornSemantics.quantify_satisfies`、`rule_satisfies`、`local_rule_satisfies` | 各 2 | 各 0 |
| `PureSourceHorn.expr_agrees`、`condition_agrees`、`localTest` | 各 31 | 各 28 |
| `PureSourceFormula.instantiate`、`quantify`、`binaryTest` | 各 31 | 各 28 |
| `PureSourceSchemas.treeTable`、`join`、`packet` | 各 31 | 各 28 |
| `PureSourceSchemas.axiomTest` | 32 | 29 |
| `PureSourceLocalTests.currentNode`、`currentRow`、`row_agrees`、`proof_agreement` | 各 32 | 各 29 |
| `PureRosser.agreement`、`independent` | 各 32 | 各 29 |
| `PureRosserDelta0.no_closed_delta0_equivalent`（已移除 `hAgrees`） | 32 | 29 |
