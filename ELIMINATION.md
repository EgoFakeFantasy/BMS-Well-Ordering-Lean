# 支撑符号三轮消去

统计范围：`SupportAxiomBasis.intrinsic_proof.compact.axioms` 的 119 条有限支撑公理实际使用的 **64 个函数、46 个关系**。签名中没有出现在该基中的符号不计入本次三轮任务。

第一轮前已完成 16 个函数、6 个关系（含隶属），待办为 48 + 40 = 88 个。第一轮新增 9 + 20 = 29 个；第二轮新增 22 + 7 = 29 个；第三轮前两批共完成 3 个函数、8 个关系；最后两轮分别完成 9 个公理集合函数和最后 5 个函数、5 个关系。累计完成 **64 个函数、46 个关系，共 110 个，剩余 0 个**。

“完成符号定义”指：实际纯隶属公式已给出；函数有任意裸 ZFC 模型、任意参数上的存在唯一性及原规格对应；关系有原定义正文在具体阶段扩张中的逐参数等价。后续已另行完成完整公理验证与指定 Rosser 合同实例，见文末终局记录。

| 轮次 | 内容 | 函数 | 关系 | 合计 | 状态 |
| --- | --- | ---: | ---: | ---: | --- |
| 第一轮 | 基础集合、关系、顺序谓词与最小归纳集 | 9 | 20 | 29 | 定义、存在唯一性与规格对应已完成 |
| 第二轮 | 自然数、顺序算子、有限序列与递归 | 22 | 7 | 29 | 22 个函数、7 个关系全部完成 |
| 第三轮 | 语法编码、语义关系与逻辑公理集合 | 17 | 13 | 30 | 17 个函数、13 个关系全部完成 |

## 第一轮

函数（9 个）：

- `binaryUnion`
- `symmetricDifference`
- `relationConverse`
- `relationComposition`
- `membershipRelation`
- `image`
- `inductiveCore`
- `omega`
- `orderedPairReverse`

关系（20 个）：

- `isEquivalenceRelation`
- `isInjective`
- `isSurjective`
- `isBijection`
- `isTransitiveSet`
- `isLinearOrder`
- `isOrderIsomorphism`
- `isOrderIsomorphic`
- `isOrderEmbedding`
- `isOrderEmbeddable`
- `isNaturalDiscreteLinearOrder`
- `isWellOrder`
- `isFinite`
- `isEquinumerous`
- `cardinalityLeq`
- `cardinalityStrictLess`
- `isDedekindFinite`
- `isInductiveSet`
- `isUnboundedSubset`
- `isBoundedSubset`

## 第二轮

第二轮已完成 **29 / 29**。本次补齐两个序型函数及序列拼接、展平。

| 本次函数 | 状态 |
| --- | --- |
| `naturalOrderType` | 纯图、任意参数存在唯一性及原自然离散线序 guard 下的规格均已完成 |
| `naturalSubsetType` | 有界有限序型与无界返回 ω 两分支的原规格均已完成 |
| `finiteSequenceConcatenation` | 内部和长度上的拼接函数图及原规格均已完成 |
| `finiteSequenceFlatten` | 内部累积列、末值有限性、唯一性及原规格均已完成 |

四项在 `PureRoundTwoStage` 的同一实际扩张中实现；签名修正和辅助定理不单独计数。

本轮完整函数清单（22 个，标记已完成项）：

- `godelPairing`：已完成
- `naturalAddition`：已完成
- `naturalExponentiation`：已完成
- `naturalMultiplication`：已完成
- `naturalSubsetType`：已完成
- `naturalOrderType`：已完成
- `powerSetBijection`：已完成
- `indexOrder`：已完成
- `minimumDifference`：已完成
- `maximum`：已完成
- `minimum`：已完成
- `finiteSequenceFlatten`：已完成
- `finiteSequenceConcatenation`：已完成
- `nonemptyFiniteSequenceSpace`：已完成
- `finiteSequenceSpace`：已完成
- `finiteSubsetCollection`：已完成
- `transitiveClosure`：已完成
- `finiteUniverse`：已完成
- `finiteHierarchy`：已完成
- `naturalDifference`：已完成
- `omegaRecursiveSequence`：已完成
- `recursiveSequenceSpace`：已完成

关系（7 个）：

- `isNaturalNumber`
- `isHereditarilyFinite`
- `omegaPairLess`
- `isCountablyInfinite`
- `isUncountable`
- `isCountable`
- `isInfinite`

## 第三轮

函数（17 个）：

- `relatedTermSet`：已完成
- `relatedNonlogicalSymbolSet`：已完成
- `relatedFormulaSet`：已完成
- `baseLogicalAxiomSet`：已完成
- `implicationDistributionAxiomSet`：已完成
- `selfImplicationAxiomSet`：已完成
- `weakeningAxiomSet`：已完成
- `contradictionAxiomSet`：已完成
- `classicalAxiomSet`：已完成
- `explosionAxiomSet`：已完成
- `caseAnalysisAxiomSet`：已完成
- `specializationAxiomSet`：已完成
- `quantifierDistributionAxiomSet`：已完成
- `vacuousQuantifierAxiomSet`：已完成
- `equalitySubstitutionAxiomSet`：已完成
- `equalityReflexivityAxiomSet`：已完成
- `logicalAxiomSet`：已完成

关系（13 个）：

- `isTermCodeAt`：已完成
- `isTermListCodeAt`：已完成
- `isFormulaCodeAt`：已完成
- `termValue`：已完成
- `isStructure`：已完成
- `isRelatedTermListCodeAt`：已完成
- `termListValue`：已完成
- `isRelatedTermCodeAt`：已完成
- `isRelatedFormulaCodeAt`：已完成
- `modusPonens`：已完成
- `syntaxTransform`：已完成
- `isLogicalAxiomCode`：已完成
- `freeVariableOccurs`：已完成

## 第一轮证明入口

- `PureProjectTemplate.bounded_functional`：Project 分离模式转为当前纯语言实际图，并从集合母集给出唯一输出。
- `PureRelationSetOperations.functional`：二元并、对称差、关系逆、关系复合、隶属关系、像集、归纳核七个函数。
- `PureOmegaAndReverse.functional`：ω 与有序对反转。ω 的模型参数显式传入；反转只在原规格无输出时使用空集缺省图。
- `PureRoundOneRelations.graph_equation`、`definition_correct`：二十个关系按原定义依赖顺序翻译，在同一实际扩张中满足原定义。保留等价关系的非空条件、基数比较的空集分支、有界与无界谓词中的严格关系。
- `PureRoundOneRelations.dependencies_covered`：逐项检查原正文只使用已完成函数和关系，临时解释分支没有进入本轮关系成果。
- `PureRoundOneSpecifications`：对称差、逆、复合、隶属关系与像集的母集限制；复合的左右投影及逆的反转规格；ω 的归纳核不动点规格。
- `PureStageSemantics.inductive_correct`：原语言的空集／后继式归纳性与 Project 的见证式归纳性一致。
- `PureRoundOneSpecifications.omega_definition_correct`：具体扩张对任意对象候选满足原语言的 ω 定义实例。

## 原规格修正与下一轮入口

第一轮修正 `NaturalDiscreteLinearOrder` 中互换的最大／最小关系方向：最大元要求其余元素指向候选，最小元要求候选指向其余元素。这与 `minimum_spec` 及消费最小条件的 `well_order_condition` 一致。修正会改变对应源句及其 quotation；本版本重新构建相关证明，不声称与修正前源码逐字相同。

第二轮已将 `minimumDifference` 从两个参数改为四个参数：源关系、源载体、第一函数、第二函数。项构造、记号和原定义实例同步更新；quotation 按当前签名重新构建。本次已完成其纯图、任意输入存在唯一性，以及原良序与不同映射 guard 下的规格；签名修复本身不单独计数。

自然减法的递推式已修正为 `g(i) = S(p)` 且 `g(S(i)) = p`；零分支保持零。原式错误地将前驱值放到了索引位置。递归序列已修复嵌套变量槽位，并将序列中的当前项改为 `⟨i, current⟩`；递归器输入仍为 `⟨current, i⟩`。`NaturalArithmeticSemantics.difference_step_correct` 和 `recursion_step_correct` 对任意源模型、任意环境证明公式与上述语义等价。这些源句和 quotation 的改变已纳入正常全库构建。

## 第二轮证明入口

- `PureOrderExtrema.functional`：最小元、最大元的实际纯图和任意输入存在唯一性；非对称性保证输出唯一，无合法极值时取空集。
- `PureOrderExtrema.minimum_spec_of_wellOrder`、`spec_of_naturalOrder`：从原良序或自然离散序 guard 推出极值存在，再证明与原规格逐输出一致，无需另加极值存在假设。
- `PureStageTwoBase`：实际替换两个函数图，其余已完成函数保持第一轮图。
- `PureNaturalRelations.graph_equation`、`definition_correct`、`dependencies_covered`：六个关系沿原定义翻译，且只消费已完成依赖。保留可数性的原满射约定和 `omegaPairLess` 的原条件，没有另加其为标准配对良序的结论。
- `PureStageTwoSemantics`：统一模型扩张、第一轮二十个关系的定义保持，以及原良序最小元、自然离散序最小元和最大元的逐参数定义实例。

## 第二轮收集与序列函数的证明入口

- `Project.FromFirstOrder.translate`、`freeClosed`、`correct`：任意当前纯公式转为自由闭合的 Project 正文；在任意外延模型中保持语义。
- `PureSeparation.exists_subset`、`bounded_functional`：任意纯正文直接消费原 ZF 分离模式；具有集合母集的成员条件给出实际图及唯一输出。
- `PureBoundedDefinitions.functional`、`graph_correct`：有限子集收集、幂集二值编码图、指数序按原成员条件分离，保留原规格的母集限制。
- `PureFiniteSequenceSpace.mapping_bounded`、`functional`、`graph_correct`：内部有限序列均为 `ω × source` 的子集，整个序列空间从其幂集中分离。未假定模型标准或序列外部有限。
- `PureSequenceFilters.functional`、`graph_correct`：非空有限序列空间与递归序列族从已构造的有限序列空间分离。
- `PureSequenceStage.omega_functional`、`omega_specification`：原 `omegaRecursiveSequence` 是递归序列族的并集，给出其纯图、任意输入存在唯一性与原并集规格。
- `PureSequenceStage.bounded_specification`、`finite_sequence_specification`、`filter_specification`：七个新函数的原规格在最后同一扩张中同时成立；`round_one_definition_correct` 和 `natural_definition_correct` 保留已完成关系的原正文。

跨阶段规格保持使用纯翻译相同的语义传输，不反复展开模型选择项。七个函数的全部依赖已检查为完成符号。

这里已经完成递归序列族及其并集的定义，并未将“合法递归器下该并集是 ω 上的总递归函数”的单独结论计为成果。

## 本次最小差异点与递推唯一性

- `PureMappingSpecifications.mapping_ext`：同域映射逐点有共同取值时，两个函数图相等。
- `PureMinimumDifference.difference_exists`、`difference_set_exists`、`exists_of_guard`：由不同的同域映射得到非空差异点集，纯分离构造该集，原良序给出最小差异点。没有额外假定差异点或极值存在。
- `PureMinimumDifference.unique`、`functional`、`agrees`：线序保证最小差异点唯一；纯总化图在任意参数上存在唯一，原 guard 下逐输出等价于原规格。
- `PureDifferenceStage.definition_instance_correct`：当前实际扩张对任意源项与任意环境满足原最小差异点定义实例。七个收集与序列函数的原规格、已有二十六个关系正文继续成立。
- `PureNaturalInduction.pure_induction`、`source_induction`：实际公式先用分离构造性质集，再消费模型内部最小归纳集的归纳核；未假定外部标准性或对任意外部谓词的归纳。
- `PureNaturalInduction.omega_recurrence_ext`、`finite_recurrence_ext`：相同初值且递推保持相等的两个函数图相等，有限长度允许为模型内部非标准自然数。
- `PureArithmeticRecurrence.specification_correct`、`iteration_unique`、`specification_unique`：加、乘、幂原规格对应有限迭代，原自然数 guard 下输出唯一。迭代唯一性对任意给定后继步函数成立；该模块记录此前的唯一性结果；本次存在性及实际扩张由下面的新模块完成。

## 本次算术、内部迭代与集合构造

- `PureOrdinalArithmetic.functional`、`sequence_exists`：用 Project 序数算术的替换收集内部有限值列，给出加、乘、幂的实际纯图、存在唯一性与自然数封闭性。
- `PureArithmeticSpecifications.iteration_exists`、`specification_correct`：内部有限值列满足原初值、后继步和末值要求，原自然数 guard 下逐输出等价于三个实际算术函数值。
- `PureGodelPairing.functional`、`agrees`：内部自然数三歧性选择原两分支，消费已完成的算术图，保留原 Gödel 配对规格。
- `PureOmegaIteration.functional`、`iterates_of_graph`：可由自由闭合 Project 二元 schema 表示的总唯一后继算子具有内部 ω 递归图，明确证明函数性、精确定义域、初值和后继方程。该定理不假设外部标准性或外部良基性。
- `PureSetIterations.hierarchy_functional`、`hierarchy_iterates`：从空集内部迭代幂集；`PureSetStage.hierarchy_specification` 对应原有限层级公理。
- `PureTransitiveClosure.exists_closure`、`unique`、`functional`：从源集内部迭代并集，再并值域，得到包含源集的唯一最小传递集。最小性使用实际子集公式的内部归纳。
- `PureFiniteUniverseStage.universe_axiom`、`hereditary_instance`：有限宇宙是层级值域之并，遗传有限关系是传递闭包的有限性，两者均按原正文给出纯定义。
- `PureNaturalDifference.union_step`、`iteration_exists`、`functional`、`agrees`：有限序数的并集等于截断前驱；限制内部并集迭代到右参数的后继，得到原减法的有限映射见证，内部递推外延性保证输出唯一。
- `PureNaturalDifferenceStage`：算术与集合构造阶段，统一保留此前九项规格、原七项收集／序列规格、最小差异点及此前关系正文。全部新模块均进入默认构建图。

上述通用 ω 迭代直接使用 Project 递归定理。原 `omegaRecursiveSequence` 所选递归序列族并集在合法递归器下的全域性仍是一个独立待办，不能混同为本次已证明。

本次还修正 `NaturalSetTheory` 的两个序型规格：自然序型的目标关系改为候选载体上的 `ε(candidate)`；有界自然数子集序型的源关系改为 `ε(subset)`。原先使用完整 `ε(ω)` 与有限载体不匹配，违反原线序定义中的关系载体限制。源句及 quotation 按修改后的定义重新构建；这两项修复不计作序型函数消去。

## 第二轮最后四项：已完成

| 函数 | 已核验的实质证明 |
| --- | --- |
| `naturalOrderType` | `PureOrderSemantics` 将原线序、极值、双射和序同构接入 Project；`PureFiniteOrderTypes` 用良序坍缩构造序型，并用原最大元条件排除无限序型。任意原规格候选也给出同一坍缩值域。 |
| `naturalSubsetType` | `PureBoundedNaturalOrder` 从最小严格上界的前驱得到最大元；有界子集因而有内部有限序型。`PureNaturalSubsetType` 同时处理无界时输出 ω 的分支。 |
| `finiteSequenceConcatenation` | `PureFiniteSequenceCore` 给出内部加法分段、消去与不相交性；`PureReplacement` 收集纯公式所定义的函数图，`PureSequenceConcatenation` 证明和长度上的存在唯一性。 |
| `finiteSequenceFlatten` | `PureFlattenRecursion` 将携带族参数的纯历史算子送入内部递归，得到长度为族长度后继的累积列；`PureSequenceFlatten` 用实际公式的内部归纳证明各步有限，并由递推唯一性确定末值。 |

四个模块的 `functional` 均给出任意参数上的总唯一性，`agrees` 在原 guard 下精确保留原规格。非法输入上的空集缺省不被解释为原支撑公理的额外结论。

`PureRoundTwoStage.order_type_definition`、`subset_type_definition`、`concatenation_definition`、`flatten_definition` 在同一最终扩张中逐参数满足四项完整原定义实例。`PureRoundTwoSpecifications` 保持旧加乘幂减、配对、收集、序列、层级、宇宙、闭包、最小差异点及关系正文。所有新增模块均进入默认导入图。

证明既不假定模型内部 ω 外部标准，也不以外部递归替代内部有限累积。自然序型规格使用前次修正后的载体限制，没有再修改源句或 quotation。

## 第三轮首批：五个符号已完成

| 符号 | 种类 | 实现与原规格 |
| --- | --- | --- |
| `isTermCodeAt` | 关系 | 最小不动点的项标签切片，满足原项码递归定义 |
| `isTermListCodeAt` | 关系 | 同一集合的参数列标签切片，保留内部长度与原递归定义 |
| `isFormulaCodeAt` | 关系 | 同一集合的公式标签切片，满足原公式码递归定义 |
| `relatedNonlogicalSymbolSet` | 函数 | 复用 ω 的实际纯图、存在唯一性，满足原常量等式 |
| `isStructure` | 关系 | 逐字翻译原结构正文，保留非空载体、定义域和三类解释条件 |

- `Automation.PredicateExpansion`：关系原子替换的语义正确性、参数模板与模型更换的对应，以及正出现谓词的单调性。函数项保持既有解释。
- `PureLeastFixedPoint.functional`、`fixed`：在给定集合界内，用纯分离构造所有闭合集合的共同成员及其一步像；单调性给出精确不动点方程。未使用模型 ω 的外部标准性、外部良基性或不可分离的任意外部谓词。
- `PureSyntaxOperator`：三个原正文组成带标签的共同生成算子；证明正性、单调性以及 `ω × (ω × (ω × ω))` 集合界。递归原子先换成候选集合成员关系，再进入纯语言翻译，避免循环展开。
- `PureSyntaxFixedPoint`：Kuratowski 元组与三个标签的单射性保证切片精确分解共同方程；`graph2`、`graph3` 是实际纯关系图。
- `PureSyntaxStage`、`PureStructureStage`：任意裸 ZFC 模型扩张，在同一模型中满足三项原递归定义、非逻辑符号全集等式及结构正文。第二轮四个末尾函数的完整定义实例继续成立。
- `PureRoundThreeSpecifications`：保持既有算术、收集／序列、集合构造、最小差异点及关系正文；全部新模块接入默认构建。

本批建立所选最小不动点解释并证明原递归方程，未额外声称所有可能递归解释均相等，也未将既有 AST / quotation 解码定理重新计数。

相关语法识别及其收集集合已由下一节完成。此前核对发现 `LogicalRuleEncoding` 的模式见证误用全称量词；此问题现已在下面的收尾第一轮修正。`logical_axiom_code_closed_condition` 的真正全称闭包保持不变。

## 第三轮第二批：六个符号已完成

| 符号 | 种类 | 实现与原规格 |
| --- | --- | --- |
| `isRelatedTermCodeAt` | 关系 | 每个符号集上的项码不动点切片，满足原递归定义 |
| `isRelatedTermListCodeAt` | 关系 | 同一符号集参数下的项列表切片，保留原深度和长度参数 |
| `isRelatedFormulaCodeAt` | 关系 | 同一符号集上的公式码切片，满足包括全称分支在内的原递归定义 |
| `relatedTermSet` | 函数 | 从内部 ω 分离存在某深度的相关项码，任意参数存在唯一 |
| `relatedFormulaSet` | 函数 | 从内部 ω 分离存在某深度的相关公式码，任意参数存在唯一 |
| `modusPonens` | 关系 | 原三个公式码的良构性条件与蕴涵码等式的纯翻译 |

- `PureRelatedSyntaxOperator`：符号集保留为纯图参数，三个正正文共用原 Kuratowski 四元组及内部 ω 乘积界。候选算子只查询固定参数的切片；本层全部其他依赖由第二轮实际图覆盖。
- `PureRelatedSyntaxFixedPoint.state_graph`、`state_unique`、`equation`：逐符号集消费既有内部最小不动点定理；复用普通语法层的查询图和元组单射性，不重新构造编码基础。
- `PureRelatedSyntaxStage.condition_satisfaction`：核验原正文的每次递归调用保留当前符号集，因而各参数的切片可以装配为整体关系解释。不能把候选算子中的参数省略推广到任意改变参数的递归正文。
- `PureRelatedSyntaxSets.member_bounded`、`functional`、`graph_correct`：原存在深度量词保持不变，由递归方程中的自然数 guard 得到 ω 集合界，再以纯分离和外延性给出两个集合的存在唯一性与原成员规格。
- `PureRelatedStage`：本批六个符号在统一模型中实现。两个集合函数的完整原定义实例、三个相关语法原定义和分离规则正文均已核验；非法符号集上的所选总定义不作为原理论的额外断言。
- `prior_function_graph`、`prior_relation_graph`：此前已计入完成清单的全部实际图保持不变。`inherited_specification` 与 `prior_transfer` 提供原正文纯翻译相同时的规格传输；上一批三项普通语法、非逻辑符号全集、结构定义及第二轮最后四项完整定义已具体传输到本阶段。

第三轮第二批的默认入口为 `PureRelatedStage`。该批不修改原源句、签名或 quotation，不新增回归样本、证明占位或对象公理。

该批之后的 14 个函数和 5 个关系，已由下面两轮全部完成。

## 最后两轮：第一轮九个函数已完成

依赖核对后，最后两轮按 **9 + 10** 分组。特化、空量化、等式替换及逻辑公理闭包依赖尚未消去的语法变换或自由变量出现关系，因此第一轮先处理不依赖它们的九个集合。不能用临时假解释制造空的公理集合并计为完成。

| 本轮已完成函数 | 模式 |
| --- | --- |
| `implicationDistributionAxiomSet` | 蕴涵分配 |
| `selfImplicationAxiomSet` | 自蕴涵 |
| `weakeningAxiomSet` | 弱化 |
| `contradictionAxiomSet` | 矛盾 |
| `classicalAxiomSet` | 经典 |
| `explosionAxiomSet` | 爆炸 |
| `caseAnalysisAxiomSet` | 分情况 |
| `quantifierDistributionAxiomSet` | 全称量词分配 |
| `equalityReflexivityAxiomSet` | 等式自反 |

- 修正 `LogicalRuleEncoding`：12 种模式成员条件及公理码生成步骤中的模式参数使用存在见证；真正的 `logical_axiom_code_closed_condition` 继续使用全称规则。修正改变相应源句及 quotation，全部依赖按修正后的源码重建。它不是与旧源句逐字相同的重构，也不单独计作符号消去。
- `PureStructuralCodeBounds`：实际 Gödel 配对、有限 numeral、字段列与结构节点保持模型内部 ω；项码与公式码的自然数界来自已构造识别不动点的原 guard。这里不把自然数界误当作良构性。
- `PureLogicalSchemaSets.constructor_natural`、`condition_bounded`：九种模式保留修正后的原存在参数与良构性条件，成员正文自身给出 ω 界，没有另加源 guard。`functional` 与 `graph_correct` 用纯分离、外延性给出实际集合图、存在唯一性与精确成员规格。
- `PureLogicalSchemaStage.membership_specification`：九项规格在同一个实际扩张中成立；`propositional_axioms` 验证七项命题公理模式的整个源闭句，另外给出量词分配和等式自反的逐码定义。
- `prior_function_graph`、`prior_relation_graph` 保留此前全部已完成实际图；`function_preserved`、`transfer`、`inherited_specification` 提供已完成函数与原规格正文的传输。新模式正文的依赖全部经 `dependencies_covered` 核验。

这批的统一入口为 `PureLogicalSchemaStage`。后续一轮已补齐依赖它的三个模式、完整量词与等式公理族，以及最终逻辑公理集合，见下节。

### 最后两轮：第二轮十个符号全部完成

| 种类 | 已完成符号 | 实现与原规格 |
| --- | --- | --- |
| 关系 | `syntaxTransform` | 七个内部自然数坐标上的正递归不动点图，精确满足原变换方程 |
| 关系 | `freeVariableOccurs` | 三坐标出现图，保留三种语法类型及原递归分支 |
| 函数 | `specializationAxiomSet` | 使用实际打开 bound 变换图，纯分离给出原模式集合 |
| 函数 | `vacuousQuantifierAxiomSet` | 保留自由变量不出现条件与实际 closeFree 分支 |
| 函数 | `equalitySubstitutionAxiomSet` | 使用实际自由代入图，保留原等式替换模式 |
| 函数 | `baseLogicalAxiomSet` | 全部 12 个实际模式集合的精确成员并集 |
| 函数 | `logicalAxiomSet` | 原生成正文的内部最小不动点，满足基集包含、全称闭包与生成规格 |
| 关系 | `isLogicalAxiomCode` | 实际逻辑公理集合的成员图，满足原识别定义 |
| 关系 | `termValue` | 固定载体、解释、符号集、赋值四参数的求值不动点切片 |
| 关系 | `termListValue` | 同一不动点中的项列切片，原递归调用的四参数保持已证明 |

- `PureNaturalTuple`：内部自然数坐标的 Kuratowski 元组、单射性及集合界。`PureSyntaxTransform`、`PureFreeVariableOccurs` 用正性、内部纯分离和不动点方程给出实际图；`PureTransformStage` 核验两项原定义及跨阶段传输。
- `PureTotalCodeBounds`：所选总化配对及结构码对任意输入仍落在内部 ω；这是实际扩张的值域性质，没有新增原源句的 guard，也不宣称非法输入满足额外配对规格。
- `PureDependentSchemaSets`：补齐三种依赖变换与出现关系的模式，纯分离和外延性给出任意参数存在唯一性。`PureAllSchemaStage` 满足全部 12 个集合的成员规格，以及命题、量词、等式三族的整个源闭句。
- `PureLogicalClosure`：基集纯图与原生成算子的集合界、单调性、不动点和唯一所选图。`PureLogicalStage.logical_code_axioms` 验证包含基集、全称闭包、生成条件及识别定义的完整源闭句；没有把所选最小不动点的唯一性扩大为任意递归解释唯一。
- `PureValueOperator`：四个外层参数固定，项结果落在载体、项列结果落在内部 ω，使用 `ω × (ω × (ω × (carrier ∪ ω)))` 作为共同集合界。`PureValueFixedPoint` 给出纯图和切片；`PureValueStage.parameters_preserved` 核验原正文每次递归调用保留四参数，因而实际整体关系满足原互递归方程。
- `Automation.RelationalCongruence`：按源语法和依赖覆盖比较解释，避免展开大型纯图。`Automation.PredicateCongruence`：把关系原子层的逐点等价传到任意正文。具体源公式的形状分析先在抽象模型中证明，再传到实际扩张。
- 最新默认入口为 `PureCompletedStage`：保留此前全部实际图，两个求值原定义在当前统一扩张中逐参数成立，逻辑公理码及全部模式公理闭句也已传入同一模型。

本轮新增 **5 个函数、5 个关系**，第三轮 **30 / 30**，总计 **110 / 110**。未改变上一版源签名、公理正文或 quotation；没有使用模型内部 ω 的外部标准性或外部良基性。

## 完整消去与独立待办

`PureCompletedStage` 已为有限支撑基涉及的 **64 个函数、46 个关系** 提供实际纯解释；本清单中没有依靠临时空集或假谓词解释的剩余符号。未在这 119 条公理中出现的签名符号不属于本次统计范围。

全部 119 条支撑公理及原无限参数族现已由 `PureSupportModels.support_models` 统一验证。`PureZFCModels.models` 覆盖原 ZFC 公理像及整个原理论；`translated_models` 覆盖其实际纯翻译，`expands` 和 `reduction` 已实现两个方向的模型保持。实际纯句子及两套公平调度现已由 `PureRosser`、`PureRosserSchedule` 固定，纯固定点有正式推导。`PureRosser.agreement_iff_comparison` 把任意原模型上的句子对应归约为比较式对应；该对应已由 `PureRosser.agreement` 证明，`PureRosser.independent` 填满合同并得到裸 ZFC 一致性下的终局。原递归序列族并集在合法递归器下的全域性仍是独立待办。`RelationalTranslation.derives_sound` 仅传输模型真值；现在 `PureRosser.translate_derives` 配合固定调度和强完备性进一步传输正向推导，仍不能代替反向保守性。

验证使用正式定理的正常 `lake build`；三轮全部模块均已纳入默认导入图。没有新增样本回归、`#eval`、`example`、`sorry`、`admit` 或对象公理。


## 统一验证（2026-09-08）

原基为 108 个具体闭句加 11 个参数分离模板，共 119 条。统一组合沿原基的 132 个节点进行；全部逐项证明入口见 [UNIFIED_VERIFICATION.md](UNIFIED_VERIFICATION.md)。

本轮纠正两处纯图与原公理的不匹配：反转函数对任意输入组合两个已总化投影；复合函数的书写参数顺序经 `relationComposition_order` 接到执行顺序。源公理与 quotation 未因这两项修正而变更。


## Rosser 配置（2026-09-08）

新增 `PureRosser.sentence`、`comparison`、`fixed_point`、`agreement_iff_comparison`，
以及 `PureRosserSchedule.source`、`target`。纯句子和调度已不再是未定参数，
该配置阶段剩余的比较式对应现已补齐，见文末终局记录。
三个新模块全部进入默认构建，`lake --wfail build` 通过 776 个任务，零错误、零警告。

## Agreement 基础对应与码域边界（2026-09-08）

`PureSourceNumerals` 已完成空集、后继、全部标准 numeral、quotation 取值和标准证明码真值对应；
`RosserDomainBoundary.domain_agrees` 已完成后继码域对应。后者还正式证明：ω 满足码域条件而 ω 不属于 ω，
所以不能从码域推出配数公理的自然数 guard。原配数定义在非自然数首参数上的实例自动成立。
完整证明树只约束编码后的根节点属于 ω；这不能直接给出输入码的自然数性。
未证明整个原理论存在使指定 Rosser 句子真值改变的扩张，故尚不能否定 `Agreement`。

该阶段先完成通用 `NaturalProofPresentation` 包装及具体候选，保留原检查器、
完备性及全部标准码的正负表示。当时尚未接入 Rosser；后续迁移见下节。
三个新模块进入默认构建，`lake --wfail build` 通过 **779 个任务，零错误、零警告**。

## 内部自然数 Rosser 迁移（2026-09-08）

用户批准切换后，`ReducedNaturalProofPresentation.presentation` 已接入源 Rosser，
固定点及其 quotation 随之重建。`ReducedRosser.fixed_point`、`independent` 与
`PureRosser.fixed_point` 均重新验证；没有修改源签名、公理或 quotation 编码规则。

`PureSourceInfinity` 从原归纳集定义及归纳核方程证明原模型和规范重扩张的内部 ω 相同，
并证明自然数元素仍在 ω 内及自然数三歧性。`RosserDomainBoundary.natural_in_domain`
保证旧后继码域在自然数上冗余。`PureNaturalRosserAgreement.comparison_naturals`
将实际比较式精确归约到内部自然数见证及其初始段上的原完整证明图。

`agreement_of_natural_proofs` 已连接这项归约与实际 `PureRosser.Agreement`。
该阶段留下的两项 `ProofAgreement`（全部内部自然数证明码上的对象图对应）现已由文末终局增量填入。
不能将标准码对应推广为内部非标准码对应。默认构建通过 **783 个任务，零错误、零警告**。

## 支撑语言 Δ₀ 与实际轨迹对应（2026-09-08）

`NaturalProofPresentation.comparison_delta0` 用比较式已有的 `code ∈ ω` 正位置 guard
证明外层存在量词有界；原图和更小码搜索本来已有 Δ₀ 证书。
`ReducedRosser.predicate_delta0` 分类实际比较式，`delta0Sentence` 为其否定。
既有 `fixed_point` 给出与当前 Rosser 句子的普通推导等价，
`delta0Sentence_independent` 保留仅假定原支撑理论一致性的双侧不可证性。
本次没有再次改变当前源句子、公理或 quotation。

这里的 Δ₀ 是相对于含 ω、幂集及编码函数的支撑语言。纯关系式翻译引入的输出见证
尚未给出同等级分类；量词 `∃ p ∈ ω` 也不等于算术语言中的有界量词。
后续纯隶属层级核验须显式处理集合界和函数图，不能将这次相对分类冒充该结论。

`PureSourceBounds.power_agrees` 证明任意输入的幂集值保持，`trace_bound_agrees`
证明实际轨迹界 `P(ω)` 保持，`trace_row_natural` 保证其中每行属于内部 ω。
`ReducedProofPresentation.graph_condition` 将实际完整图连接到具体行测试；
`PureNaturalRosserAgreement.proof_trace` 给出精确轨迹语义，
`proof_agreement_of_rows` 证明根编码取值对应及候选轨迹内行对应足以得到 `ProofAgreement`。
当时根编码所需的内部算术/配数取值对应和具体局部行检查均待证明；前者由下述算术编码增量补齐，后者与 `Agreement` 由最后的终局增量完成。

两个新模块和四个已有 Lean 文件修改进入默认构建，通过 **785 个任务，零错误、零警告**。
审计未发现 `sorryAx` 或新增可信公理，沿用原有原生计算依赖。

## 纯隶属 Δ₀ 核验：闭句限制与参数矩阵（2026-09-08）

此前把无参数纯 Rosser 闭句的 Δ₀ 分类作为待办，需要纠正。纯签名 `ℒ` 没有常元
或函数，唯一关系为二元 ∈；因此没有闭项可作为最外层有界量词的界，也没有闭关系原子。
`Automation.FunctionFreeDelta0.closed_decided` 证明每个这样的闭 Δ₀ 公式或其否定都有
普通逻辑推导。`PureRosserDelta0.sentence_not_delta0` 与 `comparison_not_delta0`
进一步直接证明当前两个纯闭句均非 Δ₀，不依赖 `Agreement` 或一致性。
`no_closed_delta0_equivalent` 在 `Agreement` 与一致性下排除任何 ZFC 可证明等价的闭 Δ₀ 代表。

正向结果为只含 ∈、具有三个集合参数的矩阵：

```text
δ(w,A,B) := ¬∃ p∈w, p∈A ∧ ∀ q∈p, q∉B
```

`matrix_delta0` 是其实际纯语言语法证书。`proofCondition` 使用原完整对象证明图的
实际纯翻译；`parameters_exists` 与 `parameters_unique` 从裸 ZFC 的纯分离和外延性
给出唯一的 `w=ω` 及两侧自然数证明码集合 `A,B`。这些集合解释的是规范扩张中的
原支撑证明图，不是纯语言自身 quotation 的新证明系统。
`sentence_iff_matrix` 连接当前纯 Rosser 真值，`representation_derives` 给出普通推导：

```text
ZFC ⊢ R ↔ ∃ w,A,B, Def(w,A,B) ∧ δ(w,A,B)
```

`Def` 保留集合参数的完整定义及其量词，未证明为 Δ₀；`representation_not_delta0`
证明整个存在闭句不是 Δ₀。不能将参数矩阵的分类报告为原证明谓词或完整纯闭句的
复杂度下降。当时尚缺内部算术/编码取值及局部行对应；最新进展见下节。

两个新增模块和三个已有 Lean 文件修改进入默认构建，通过 **787 个任务，零错误、零警告**。
18 个接口的可信依赖审计无 `sorryAx`，没有新增原生计算证书或自定义公理。


## 内部算术与编码对应（2026-09-08）

三个新模块完成任意原模型与其规范重扩张之间的算术编码取值对应。输入可以是非标准内部自然数。

1. `PureSourceMappings` 从原公理确定 Kuratowski 有序对、关系和函数的纯语义。`mapping_project` 把每个原合法映射识别为同一纯约化中的集合函数；`application_agrees` 确定原定义域内的求值。
2. `PureSourceArithmetic` 将实际原加乘幂规格的有限递推见证送入已有内部集合函数唯一性接口。初值与后继先对应，加法确定后再确定乘法，随后确定幂。归纳性质为实际集合函数的值相等，没有模型外标准性假设。
3. `PureSourceCoding` 完成原 Gödel 配对两分支、字段列与任意标签节点的对应，保留内部自然数封闭性。quotation 通过既有求值定理处理。
4. `PureNaturalRosserAgreement.root_natural`、`root_agrees` 直接覆盖当前完整证明图的实际根值。`proof_agreement_of_rows` 已删除 `hRoot` 参数，由证明自动填入；现在只要求候选轨迹中的局部行真值对应。

源签名、公理、固定点和 quotation 未改变。没有声称任意非法算术或求值参数上的解释相同；没有证明原递归谓词在全部输入上唯一。这一阶段留下的局部行对应及终局已在下一节完成。

`lake --wfail build` 通过 **790 个任务，零错误、零警告**；20 个接口审计没有 `sorryAx` 或新增原生可信依赖。新增源码为三个模块，修改一个已有 Lean 模块，未增加测试样本、原生证书、自定义公理或未完成证明。


## 实际局部行对应及裸 ZFC Rosser 终局（2026-09-08）

六个新增模块完成从实际检查公式到指定纯句子的最后连接：

1. `Automation.ObjectHornSemantics` 给出任意模型中有界见证块、规则矩阵和有限局部查询的精确语义。
2. `PureSourceHorn` 在同一集合轨迹上比较规则；参数落入自然数行的后继，表达式取值因而受已有对应定理控制。
3. `PureSourceFormula` 组合自然数项、公式联结、模板代入与内部有界量词。
4. `PureSourceSchemas` 覆盖实际有限公理表、分离/收集/替换模式的重命名与中间码连接，得到 `axiomTest`。
5. `PureSourceLocalTests` 复用实际语法、变换、逻辑公理、六种节点及行规则表，证明 `row_agrees` 和任意固定结论的 `proof_agreement`。
6. `PureRosserComplete` 给出 `PureRosser.agreement` 及 `PureRosser.independent`。最后定理只要求 `Derives.Consistent PureModel.theory []`，不再要求调用者提供真值对应。

源公理、签名、quotation、固定点及三参数纯 Δ₀ 矩阵未改变。证明允许非标准内部自然数，
没有将标准正负实例直接推广为反射公理。完整闭句非 Δ₀；`no_closed_delta0_equivalent` 已用新终局消去 `hAgrees` 参数。
完整默认构建通过 **796 个任务，0 错误，0 警告**；可信依赖审计见 `UNIFIED_VERIFICATION.md`。
