# YesMetaZFC Lean 形式化奖杯表

更新日期：2026-09-08。当前已完成 **裸 ZFC 上的具体 Rosser 独立句实例**。
本表直接登记参与正常构建的声明；分轮计数记录各阶段进度，当前总量以本节为准。

## 当前终局：裸 ZFC Rosser 独立性

目标理论为纯集合论语言中的 `PureModel.theory`，具体闭句为 `PureRosser.sentence`。
记该句子为 $R$，已证明：

$$
\operatorname{Con}(\mathrm{ZFC})\Longrightarrow
\bigl(\mathrm{ZFC}\nvdash R\bigr)\land\bigl(\mathrm{ZFC}\nvdash\neg R\bigr).
$$

$R$ 只含隶属关系、等号与逻辑符号，是当前源 Rosser 句子的实际纯翻译。
最终定理只有裸 ZFC 一致性前提；真值对应 `Agreement` 已有证明。

| 里程碑 | 实际声明 | 源码 |
| --- | --- | --- |
| 具体纯句子与固定点 | `PureRosser.sentence`、`fixed_point`：固定当前纯闭句，并给出裸 ZFC 中与比较式否定等价的普通 Hilbert 推导。 | [PureRosser](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosser.lean) |
| 任意原模型上的句子对应 | `PureRosser.agreement`：源句子与实际纯翻译在原模型及其纯约化中真值一致。 | [PureRosserComplete](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserComplete.lean) |
| 裸 ZFC 双侧不可证性 | `PureRosser.independent`：仅由裸 ZFC 一致性得到 $R$ 与 $\neg R$ 均不可证。 | [PureRosserComplete](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserComplete.lean) |
| 三参数纯 Δ₀ 矩阵 | `PureRosserDelta0.matrix_delta0`、`parameters_exists`、`parameters_unique`、`representation_derives`：参数存在唯一，且与当前句子有裸 ZFC 中的实际推导等价。 | [PureRosserDelta0](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserDelta0.lean) |
| 无参数闭 Δ₀ 代表的排除 | `PureRosserDelta0.sentence_not_delta0`、`no_closed_delta0_equivalent`：当前闭句非 Δ₀；仅假定裸 ZFC 一致，排除一切可证明等价的无参数纯 Δ₀ 闭句。 | [PureRosserDelta0](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserDelta0.lean) |

纯 Δ₀ 矩阵具体为
$\delta(w,A,B):=\neg\exists p\in w\,(p\in A\land\forall q\in p\,q\notin B)$。
参数定义使用纯 ZFC 分离，完整存在闭句非 Δ₀；矩阵分类与闭句独立性分别登记。

## 支撑消去、公理验证与非标准模型对应

有限支撑基实际使用的 **64 个函数、46 个关系，共 110 个符号已全部消去**。
**119 条有限基公理**及其覆盖的原无限参数族已统一验证。内部自然数可以非标准；
对应证明使用实际集合函数和集合轨迹，保留各原规格的合法输入条件。

| 已完成成果 | 实际声明 | 源码 |
| --- | --- | --- |
| 完整支撑理论模型验证 | `PureSupportModels.support_models`：规范扩张满足整个原支撑理论。 | [PureSupportModels](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSupportModels.lean) |
| 原 ZFC 公理与纯翻译验证 | `PureZFCModels.models`、`translated_models`：扩张满足原 ZFC 公理像和支撑理论，裸 ZFC 模型满足全部实际纯翻译。 | [PureZFCModels](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureZFCModels.lean) |
| 扩张与约化 | `PureZFCModels.expands`、`reduct_models`、`reduction`：裸 ZFC 模型可扩张，任意原模型可约化。 | [PureZFCModels](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureZFCModels.lean) |
| 合法映射及求值对应 | `PureSourceMappings.ordered_agrees`、`mapping_project`、`application_agrees`：同一纯约化中的有序对、集合函数及原定义域内求值对应。 | [PureSourceMappings](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceMappings.lean) |
| 内部自然数算术对应 | `PureSourceArithmetic.addition_agrees`、`multiplication_agrees`、`exponentiation_agrees`：全部内部自然数输入上的加、乘、幂取值保持。 | [PureSourceArithmetic](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceArithmetic.lean) |
| 实际编码对应 | `PureSourceCoding.pairing_agrees`、`fields_agrees`、`node_agrees`：Gödel 配对、有限字段列与节点编码保持。 | [PureSourceCoding](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceCoding.lean) |
| 有界轨迹与局部规则组合 | `PureSourceHorn.condition_agrees`、`localTest`：同一候选集合轨迹及有限局部查询的真值保持。 | [PureSourceHorn](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceHorn.lean) |
| 自然数参数公式组合 | `PureSourceFormula.instantiate`、`quantify`：实际模板代入和自然数界内见证量化保持对应。 | [PureSourceFormula](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceFormula.lean) |
| 实际公理检查 | `PureSourceSchemas.axiomTest`：固定公理表及分离、收集、替换模式中的实际中间码连接保持。 | [PureSourceSchemas](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceSchemas.lean) |
| 实际节点、行及完整证明图 | `PureSourceLocalTests.currentNode`、`currentRow`、`row_agrees`、`proof_agreement`：任意固定结论在全部内部自然数证明码上的完整对象图对应。 | [PureSourceLocalTests](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceLocalTests.lean) |

通用的有界见证块与规则矩阵语义入口是
[ObjectHornSemantics](YesMetaZFC/Automation/ObjectHornSemantics.lean) 中的
`quantify_satisfies`、`rule_satisfies`、`local_rule_satisfies`。
分轮符号清单见 [ELIMINATION.md](ELIMINATION.md)，原公理逐项验证见
[UNIFIED_VERIFICATION.md](UNIFIED_VERIFICATION.md)。

## 构建与可信边界

当前入口为 `YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory`；上表集合论模块的完整
命名空间前缀为 `YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC`。

最新完整 `lake --wfail build` 通过 **796 个任务，0 错误、0 警告**。
终局及本轮关键接口的 20 项依赖审计无 `sorryAx`，没有新增可信依赖；
`PureRosser.agreement`、`independent` 各有 32 项既有依赖，其中 29 项为既有原生计算依赖。
此次奖杯表更新只改文档，沿用已核验的证明与审计结果。

原递归序列族之并在合法递归器下为 ω 上总函数，仍是独立数学待办；其原定义已验证，
本次独立性证明使用已有内部递归接口。这项待办不再是当前 Rosser 实例的前提。

## 当前内核与支撑理论证明表示

本节保留支撑理论 `ProofT.ZFC.intrinsic_zfc_theory` 上的证明表示及逐层纯解释入口。
这些基础设施与上方裸 ZFC 终局共用当前内核。

| 声明 | 已证明的内容 |
| --- | --- |
| `Project.FirstOrderSemantics.formula_correct`、`models_iff`、`ProofT.ZFC.PureModel.project_models` | 当前类型化纯语言与 Project 任意闭合正文、句子及模型语义对应；裸 ZFC 模型接通已有集合论模型库。 |
| `Automation.SemanticTransfer.consistent_of_expands`、`Reduction.reflect`、`independent` | 用模型扩张传输一致性，用约化及指定句子真值对应经强完备性反射推导并传输双向不可证性。 |
| `Automation.TotalizedGraph.functional`、`agrees`、`fallback_of_absent` | 单值部分图的规范总化；有输出时精确保留原图，无输出时精确使用缺省图。 |
| `ProofT.ZFC.PureKuratowski.exists_code`、`code_unique`、`code_injective` | 裸 ZFC 模型中原支撑 Kuratowski 编码的存在、唯一与坐标单射。 |
| `ProofT.ZFC.PureKuratowskiProject.interpretation` | 将纯 Kuratowski 编码具体实现为 Project 集合构造库的有序对解释，四个合同字段均由裸 ZFC 定理提供。 |
| `ProofT.ZFC.PureMappingDefinitions.functional`、`isMapping_correct`、`mapping_spec` | 原笛卡尔积与映射收集函数的纯图对任意参数存在唯一；纯映射谓词与原定义域、值域规格对应。 |
| `ProofT.ZFC.PureMappingSpecifications.cartesian_spec`、`mappingCollection_spec` | 原支撑规格中的二重幂集和笛卡尔积幂集限制均由实际纯定义推出。 |
| `ProofT.ZFC.PureRelationCoordinates.functional`、`code_mem_double_union` | 定义域和值域的纯图对任意输入存在唯一输出；合法有序对坐标均属于输入的双重并集。 |
| `ProofT.ZFC.PureCoordinateSpecifications.coordinate_spec`、`mapping_definition`、`application_spec` | 关系输入上对应原投影筛选规格；以实际坐标图补齐映射定义和求值的定义域接口。 |
| `ProofT.ZFC.PureMappingOperations.functional`、`identity_spec`、`restriction_correct`、`restriction_mapping` | 恒等映射、函数限制的纯图存在唯一并符合原成员规格；映射限制到源集子集后保持原目标集。 |
| `ProofT.ZFC.PureRelationDefinitions.relationGraph`、`PureRelationFunctions.graph`、`functional` | 原符号索引下的四个新函数总图及子集、有序对、关系、函数纯定义；函数图对任意模型对象参数存在唯一。 |
| `ProofT.ZFC.PureRelationFunctions.left_spec`、`right_spec`、`application_spec` | 合法输入上总化图匹配原投影及函数求值数学规格；不额外规定原理论中的非法输入。 |
| `ProofT.ZFC.PureRosserTransfer.independent` | 精确回传合同及公平调度填满后，仅假定裸 ZFC 一致性的条件终局；具体合同现由 `PureRosser.agreement` 填满，直接终局见 `PureRosser.independent`。 |
| `ProofT.intrinsic_proof_axiom_presentation` | 全部原有支撑公理及参数化公理族都有显式证书，证书恰好覆盖原理论。 |
| `ProofT.ZFC.intrinsic_zfc_axiom_presentation` | ZFC 的固定公理、分离和收集 schema 与支撑公理统一为同一证书表示。 |
| `ProofT.ProofCertificate.nonempty_iff_provable` | 显式公理证书推导与普通 Hilbert 推导等价，覆盖全部六类推导规则。 |
| `ProofT.ZFC.intrinsic_zfc_derives_iff_certificate` | 在具体支撑理论上，可证闭句恰好是有结构证书通过结论检查的闭句。 |
| `ProofT.ZFC.intrinsic_zfc_nat_decode_sound` | 自然数成功解码为闭证书时，证书的结论在原支撑公理理论中有普通推导。 |
| `ProofT.ZFC.intrinsic_zfc_nat_check_sound` | 实际可计算的自然数检查器接受一个闭句时，该闭句在原理论中可证。 |
| `ProofT.ZFC.intrinsic_zfc_nat_check_eq_true_iff` | 接受等价于解码成功且证书结论与目标闭句完全相同。 |
| `ProofT.ZFC.intrinsic_zfc_nat_decode_encode` | 任意结构闭证书从其自然数编码恢复为同一个证书。 |
| `ProofT.ZFC.intrinsic_zfc_nat_encode_injective` | 不同的结构闭证书具有不同的自然数编码。 |
| `ProofT.ZFC.intrinsic_zfc_derives_iff_nat_certificate` | 普通可证性等价于存在一个被自然数检查器接受的证明码。 |
| `ProofT.IntrinsicQuotation.unquote_quote`、`quote_injective` | 当前十一种公式构造子经对象 quotation 后可反解为原公式，故新码单射。 |
| `ProofT.IntrinsicQuotation.quote_ne` | 不同公式的新码在任何提供原 `CertificateCore` 的对象理论内可证明不等。 |
| `ProofT.ZFC.SchemaConclusion.positive`、`negative` | 分离、收集、替换的已解析实例与任意目标闭句的结论比较有正负对象表示；原始输入的完整识别由后续 `SchemaPacket` 接入。 |
| `ProofT.ZFC.SchemaEnvelope.positive_at_tree`、`negative_at_tree` | 任意原始树的模式标签、字段数、参数叶子有统一 Delta0 正负对象表示；正文仍为未解析树。 |
| `ProofT.ZFC.SchemaEnvelope.check_of_separation_decode`、`check_of_collection_decode` | 实际模式解码器成功时，同一原始输入通过新对象外壳检查。 |
| `ProofT.ZFC.SchemaTerm.positive_at_tree`、`negative_at_tree` | 实际 `ProjectDecode.term` 的成功/失败获得作用域参数化的正负对象推导，覆盖畸形输入及越界索引。 |
| `ProofT.ZFC.SchemaBody.decode_eq_some_iff`、`check_eq_false_iff` | 整个正文的成功识别恰好对应作用域正确、自由闭合且重新编码为原树的正文；拒绝排除所有这样的正文。此为数据层规格。 |
| `ProofT.ZFC.SchemaBody.unarySchema_isSome`、`binarySchema_isSome` | 实际两类模式解码器恰好使用正文识别器，自动闭性证明不额外改变接受集。 |
| `ProofT.ZFC.SchemaRename.formula_encode_rename`、`decode_formula` | 有限表原始树重命名与类型化重命名交换，包括量词提升及任意非法输入。 |
| `ProofT.ZFC.SchemaRename.run_eq_some_iff`、`run_ne_some_iff`、`run_reject_iff` | 任意候选输出的完整数据层规格；失败覆盖源正文非法和目标表越界，包括未使用的越界表项。 |
| `ProofT.ZFC.SchemaRename.run_intrinsic`、`run_quotation` | 原始树递归直接与当前类型安全内核 AST 及新 quotation 交换，包含失败分支。 |
| `ProofT.ZFC.SchemaRename.Site.run_encode` | 任意参数数目的分离、收集、替换六个实际正文位置均使用已验证的有限表。 |
| `ProofT.ZFC.SchemaObjectGraph.Body.positive_at_tree`、`negative_at_tree` | 实际完整正文检查器的接受与拒绝推出同一个统一对象公式及其否定，覆盖全部构造子、任意作用域和畸形原始树。 |
| `ProofT.ZFC.SchemaObjectGraph.Rename.positive_at_tree`、`negative_at_tree` | 实际有限表重命名图的统一正负推导；负向覆盖任意错误候选输出及未使用的越界表项。 |
| `ProofT.ZFC.SchemaObjectGraph.Rename.site_positive`、`site_negative` | 六个实际模式位置直接使用上述对象表示，参数数目不设上限。 |
| `Automation.ObjectHorn.positive`、`negative` | 固定有限规则的接受轨迹和良基拒绝证书编译为普通 Hilbert 推导；负向排除任意对象轨迹。 |
| `ProofT.ZFC.SchemaTemplate.separation_core`、`collection_core`、`replacement_core` | 固定填槽模板逐节点等于现有三类模式核心，参数数目任意。 |
| `ProofT.ZFC.SchemaTemplate.run_isSome` | 六处实际重命名接入模板装配后，接受集精确等于源作用域的正文识别。 |
| `ProofT.ZFC.SchemaTemplate.positive_at_tree`、`negative_at_tree`、`unknown_tag_negative` | 一个带对象标签的固定 Delta0 模板图，正确填槽可推导，任意错误输出及未知标签可否定。 |
| `ProofT.ZFC.SchemaClosure.positive_at_tree`、`negative_at_tree` | 任意层数、任意原始核心与错误候选闭合结果的新树码全称前缀图。 |
| `ProofT.NatPacket.decode_eq_some_iff` | 所有成功解码的原始自然数恰是结果树的规范版本一编码。 |
| `ProofT.ZFC.NatPacketLink.positive_at_tree`、`negative_at_tree` | 原始包自然数与对象树码之间的统一 Delta0 连接；拒绝非法包及错误候选树。 |
| `ProofT.ZFC.NatPacketLink.schema_separation`、`schema_collection`、`schema_replacement` | 正文包经解析、重命名、模板和参数闭合，精确恢复实际三类模式闭句。 |
| `ProofT.ZFC.SchemaTable.positive`、`negative` | 六个实际模式位置的任意参数表由固定八条规则生成；任意错误自然数表码可否定。 |
| `ProofT.ZFC.SchemaObjectGraph.Rename.negative_number` | 重命名负向表示扩展到所有自然数候选码，包括根本不是树码的数。 |
| `ProofT.ZFC.SchemaJoin.positive`、`negative` | 固定四元 Delta0 图内部量化七个中间码，直接表示正文到实际 Project 闭句的整条流水线。 |
| `ProofT.ZFC.SchemaJoin.positive_at_tree`、`negative_at_tree` | 同一图的紧凑树项接口，非法正文和错误闭句均被拒绝。 |
| `ProofT.ZFC.SchemaJoin.separation_positive`、`collection_positive`、`replacement_positive` | 三类实际模式闭句直接得到统一图的普通推导，不再外加表生成或中间码连接合同。 |
| `Automation.ObjectPacket.negative_number` | 传输图负向覆盖任意自然数候选树码，非树和非列表中间码由严格下降的拒绝证书排除。 |
| `Automation.ObjectRawTreeBounds.packet_bound`、`ObjectProjectQuotation.run_le` | 原树码由实际包的固定初等项界定，转换前 Project 码不超过转换后的内核码，故连接不需要公开界槽位。 |
| `ProofT.ZFC.KernelQuotation.project_formula_code`、`sentence_positive` | 原始树转换逐构造子等于当前类型安全内核编码，并有对象图推导；成员、子集增加正确符号字段，等号及全部连接词、量词保持构造子。 |
| `ProofT.ZFC.SchemaKernelJoin.positive`、`negative` | 对象层隐藏 Project 闭句中间码，三类模式直接连接到当前内核 quotation；任意自然数错误候选可否定。 |
| `ProofT.ZFC.SchemaKernelJoin.separation_decode`、`collection_decode`、`replacement_decode` | 对所有原始正文，包括解码失败分支，连接结果与实际类型化 schema 解码器及当前 AST 编码相等。 |
| `ProofT.ZFC.SchemaPacket.template_delta0`、`run_eq_actual` | 固定二元模式包图隐藏外壳三槽位，端到端流程对任意包精确等于原 ZFC 公理证书解码器的两个模式分支。 |
| `ProofT.ZFC.SchemaPacket.actual_positive_number`、`actual_negative` | 任意包自然数与候选内核码的实际解码成功、失败分别推出同一固定对象公式及其否定，无额外表示合同。 |
| `ProofT.ZFC.SchemaPacket.separation_positive`、`collection_positive` | 既有分离、收集证书的版本一包直接得到当前内核 quotation 上的对象图推导；参数数目任意。 |
| `ProofT.ZFC.SchemaKernelJoin.replacement_positive` | 替换保留独立模式接口，得到当前内核 quotation 上的普通推导，不新增 ZFC 公理标签。 |
| `Automation.ObjectFiniteTable.positive`、`negative` | 任意有限数值键/树输出关系表的对象表示；保留紧凑输出，允许重复键，负向排除所有匹配行与任意错误候选自然数。 |
| `ProofT.ZFC.zfc_base_axiom_encode_of_decode`、`BaseAxiomPacket.decode_eq_some_iff` | 所有成功基础公理证书与自然数包均规范，重新编码逐节点恢复输入，包含任意参数数目的分离与收集。 |
| `ProofT.ZFC.BaseAxiomPacket.template_delta0`、`positive_number`、`negative` | 八条固定公理与两个模式共用一个二元 Delta0 图，任意包与候选自然数都有精确正负表示。 |
| `ProofT.ZFC.BaseAxiomPacket.presentation` | 完整 ZFC 基础公理关系的具体 `Delta1AxiomPresentation`，检查器可靠、完备，正负推导均在原支撑理论中完成；作为完整证明表示的公理检查层。 |
| `ProofT.SyntaxDecode.term_encode_of_decode`、`SyntaxParameters.encode_of_decode` | 当前内核完整项和 indexed 参数证书成功解码后精确恢复原树，涵盖全部 76 个函数符号。 |
| `Automation.ObjectTermSyntax.termTemplate`、`parameterTemplate` | 固定 83 条规则表示双作用域项、签名元数及 indexed 外壳；两套模板均为 Delta0，并有通用正负普通推导。 |
| `ProofT.SupportParameters.actual_eq_decode` | 新参数解码器的接受、拒绝与全部 11 类原参数公理分支对任意原始输入一致。 |
| `ProofT.ZFC.SupportParameter.positive_at_tree`、`negative_at_tree`、`encoded_positive` | 参数证书合法性在原支撑理论中有具体正负表示；任意类型正确的参数直接得到正向推导，公理结论在 `SupportAssembly`、`SupportConclusion` 接入。 |
| `ProofT.SyntaxSubstitution.formula_substitute`、`close_encode` | 原始树上的完整项代入、绑定提升及任意层数全称闭合，精确对应类型安全内核操作。 |
| `ProofT.SupportAssembly.instantiate_eq`、`close_instantiate` | 全部 11 类固定模板在任意实际项处代入并闭合，精确恢复各族原有公理。 |
| `ProofT.SupportConclusion.actual_eq_decode`、`sentence_derives` | 对任意原始输入对齐原证书的实际闭句；装配公理在对应原族理论中有普通 Hilbert 推导。 |
| `ProofT.SupportRealization.run_eq_actual`、`assemble_quote`、`packet_encode` | 计算层连接原始码装配、当前 quotation 与内层参数包；计算层交换定理；当前对象表示经有限公理基完成。 |
| `ProofT.SupportAssembly.sentence_of_closedTemplate` | 全部 11 类参数公理均由各自的一条全称闭模板作普通 Hilbert 推导，参数上下文和项深度任意。 |
| `ProofT.SupportAxiomBasis.intrinsic_proof`、`FiniteAxiomBasis.derives_iff` | 完整原支撑公理理论有内部有限公理基，并在任意自由上下文和局部假设下推导等价；去重后为 119 条闭句。 |
| `Automation.ObjectFiniteAxioms.presentation`、`ProofT.Delta1AxiomPresentation.union` | 任意有限闭句表的精确成员检查与对象正负表示，可与已有公理表示统一合并。 |
| `ProofT.ZFC.ReducedAxiomPacket.decode_encode`、`checked_agrees`、`presentation` | 原 ZFC 基础公理与有限支撑基共用同一二元 Delta0 公式；实际包解码、当前 quotation 及正负推导全部接通。 |
| `ProofT.ZFC.ReducedAxioms.derives_iff`、`liftProofPresentation` | 等价公理基与原支撑理论的所有普通推导双向传输；完整证明表示也可保持同一个对象公式传回原理论。 |
| `ProofT.bounded_exists_numeral_neg` | 标准有限界内每个实例的否定合成任意对象见证的有界存在否定。 |
| `ProofT.ZFC.SchemaQuotationAudit.no_legacy_nat_representation` | 在一致的支撑理论中，旧 Hilbert quotation 无法承载当前精确 AST 自然数检查器的统一正负表示。 |
| `ProofT.ZFC.intrinsic_zfc_rosser_assembly` | 现有证明图的有限 Rosser 比较装配。 |
| `ProofT.rosser_incompleteness` | 给定证明表示、固定点证明和一致性后的抽象 Rosser 结论。 |
| `ProofT.ZFC.ReducedProofPresentation.nodeTest`、`presentation` | 六类证明节点的具体对象测试及全树 Δ₁ 证明表示，目标为原支撑理论。 |
| `Automation.ObjectLeastWitness.unique`、`ObjectMinimumRelation.unique` | 最小合法输出与有限码域切分将标准正负实例升级为任意对象见证的唯一性。 |
| `Automation.ObjectNumeralSyntax.checked_iff`、`positive`、`negative` | 当前 numeral 项编码的实际递归规则、精确规格及任意候选输出的正负对象推导。 |
| `Automation.ObjectDiagonal.positive`、`unique` | 当前 quotation 下实际自代入关系的存在性及任意对象输出唯一性。 |
| `Automation.ObjectDiagonal.fixedPoint_spec` | 对任意固定一元模板构造实际句子，并在提供既有支撑能力的理论中证明当前 quotation 的固定点等价。 |
| `ProofT.ZFC.ReducedRosser.sentence`、`fixed_point`、`independent` | 原支撑理论上的具体 Rosser 句子、固定点证明及仅依赖一致性的双向不可证结论。 |
| `Automation.RelationalTranslation.term_correct`、`arguments_correct`、`formula_correct` | 类型安全函数图消去精确保持项值、参数值列及全部十一种公式构造子的满足关系。 |
| `Automation.RelationalTranslation.expansion_realizes`、`models_iff`、`derives_sound` | 由函数图存在唯一性构造实际源模型，连接理论模型与普通源推导的目标真值；尚非句法保守性。 |
| `ProofT.ZFC.PureModel.theory`、`PureFunctionDefinitions.functional` | 在裸 ZFC 的纯 `ℒ` 模型中，原支撑签名的空集、无序对、单集、并集、幂集、后继六种实际图均有任意参数的唯一输出。 |
| `ProofT.ZFC.PureRelationSetOperations.functional`、`PureOmegaAndReverse.functional` | 第一轮九个函数具有纯图及任意裸 ZFC 模型、任意参数的存在唯一性。 |
| `ProofT.ZFC.PureRoundOneRelations.graph_equation`、`definition_correct` | 二十个关系按原正文编译，在同一实际阶段扩张中对任意参数满足原定义。 |
| `ProofT.ZFC.PureRoundOneRelations.dependencies_covered` | 原正文只依赖已完成符号，未处理函数与关系的临时解释不进入本轮关系成果。 |
| `ProofT.ZFC.PureRoundOneSpecifications` | 原对称差、逆、复合、隶属关系和像集的母集限制，以及反转、投影、ω 归纳核规格。 |
| `ProofT.ZFC.PureStageSemantics.inductive_correct`、`PureRoundOneSpecifications.omega_definition_correct` | 原归纳集谓词对应 Project 归纳性，具体扩张满足原语言的 ω 定义实例。 |
| `ProofT.ZFC.PureOrderExtrema.functional`、`minimum_spec_of_wellOrder`、`spec_of_naturalOrder` | 极值图在任意裸 ZFC 模型上全域唯一；原顺序 guard 给出存在性和原规格。 |
| `ProofT.ZFC.PureNaturalRelations.graph_equation`、`definition_correct`、`dependencies_covered` | 自然数、无限性、可数性、不可数性、可数无限性、ω 配对序六个关系按原正文消去；依赖只含已完成符号。 |
| `ProofT.ZFC.PureStageTwoSemantics.minimum_definition_correct`、`minimum_natural_definition_correct`、`maximum_natural_definition_correct` | 同一实际扩张对任意参数满足三个原极值定义实例。 |
| `BasicSetTheory.NaturalArithmeticSemantics.difference_step_correct`、`recursion_step_correct` | 修正后的自然减法和递归序列公式，在任意源模型及环境中精确对应递推语义。 |
| `Project.FromFirstOrder.correct`、`PureSeparation.bounded_functional` | 任意当前纯公式复用原 ZF 分离模式；有集合界的正文给出唯一集合图。 |
| `ProofT.ZFC.PureBoundedDefinitions.functional`、`PureFiniteSequenceSpace.functional` | 有限子集收集、幂集二值编码、指数序、内部有限序列空间四个函数的纯定义与存在唯一性。 |
| `ProofT.ZFC.PureSequenceFilters.functional`、`PureSequenceStage.omega_functional` | 非空序列空间、递归序列族及其并集三个函数的纯定义与存在唯一性。 |
| `ProofT.ZFC.PureSequenceStage` | 七个新函数在最后同一扩张中的原规格保持，以及已有关系定义的逐参数保持；该阶段保留旧规格，完整理论验证由 `PureSupportModels.support_models` 提供。 |
| `ProofT.ZFC.PureMinimumDifference.functional`、`exists_of_guard`、`agrees` | 最小差异点的纯图在任意输入上存在唯一；原良序及不同同域映射 guard 给出原规格，无额外存在假设。 |
| `ProofT.ZFC.PureDifferenceStage.definition_instance_correct` | 该阶段实际扩张对任意源项和环境满足原最小差异点定义实例，并保留此前七项收集／序列规格与关系正文。 |
| `ProofT.ZFC.PureNaturalInduction.source_induction`、`finite_recurrence_ext` | 可分离公式上的模型内部自然数归纳，以及内部有限长度递推函数的唯一性；不要求外部标准性。 |
| `ProofT.ZFC.PureArithmeticRecurrence.specification_correct`、`specification_unique` | 加、乘、幂原规格精确对应内部有限迭代，原自然数 guard 下输出唯一；存在性已由 `PureOrdinalArithmetic.sequence_exists` 和 `PureArithmeticSpecifications.iteration_exists` 补齐。 |

自然数编解码、完整证书往返、检查器可靠性与完备性均已完成，见
[输入格式与证明接口](NAT_DECODING.md)。完整等价公理基及整棵证明树的对象正负表示
已给出具体 `Delta1ProofPresentation`。`ReducedRosser.independent` 进一步完成当前
架构下的支撑理论 Rosser 实例，唯一前提是该理论一致；裸 ZFC 的支撑消去及指定纯句子的独立性现也已完成。
公共证明表示与抽象 Rosser 使用 `IntrinsicQuotation.quote`；当前整树图为
`ReducedNaturalProofPresentation.presentation.graph`，旧 Hilbert 图仅保留历史兼容接口。
原始模式外壳、正文项作用域、完整正文识别及有限表重命名现均有统一对象公式和
真实正负推导。两套递归公式在当前扩展语言中为 Delta0；证明没有增加对象公理。
三类固定模式模板及装配步骤的正负图也已完成；其槽位仍作为输入。
参数全称闭合与自然数传输包连接也已完成各自的统一正负图，宿主模式装配已连通。
重命名表生成和模式内部七个中间码的对象存在连接现已由 `SchemaTable`、`SchemaJoin` 完成。
Project 树码到当前内核 quotation 的固定转换和正负推导，以及实际两类 ZFC 模式包的
外壳、传输包、模式流水线的完整对象存在连接现已完成。`SchemaPacket.template` 只公开
包码和候选内核码，`run_eq_actual` 独立对齐原 ZFC 公理证书解码器，覆盖失败输入。
`BaseAxiomPacket.presentation` 覆盖原 ZFC 公理像全部构造子。
参数化项族现已完成全部 11 类的证书合法性正负表示，包含全部 76 个函数符号和
双作用域项，上下文长度与项深度没有固定上限。上述性质由通用定理及 Lean 内核检查保证。
全部 11 类参数模板的代入、全称闭合、公理结论装配及 quotation 连接现已完成计算层
交换定理，并接入内层参数外壳的版本一自然数包。进一步证明的有限生成性使这 11 类
无限实例可统一由有限闭模板导出。当前采用“原基础公理像＋119 条有限支撑闭句”的
完整对象表示，普通推导与原理论已证明等价。原参数证书逐字装配关系及旧 union 路径
不再是本路线的必要节点。新公理基的完整证明树表示和实际 Rosser 固定点均已接通。
上述局部检查图的 Delta0 分类属于扩展支撑语言；纯语言参数矩阵与裸 ZFC 独立性见首页入口。



## 第二轮算术与内部迭代

| 证明入口 | 已核验成果 |
| --- | --- |
| `PureOrdinalArithmetic.sequence_exists`、`PureArithmeticSpecifications.specification_correct` | 替换收集内部有限算术值列，补齐加、乘、幂的存在唯一性及原规格对应。 |
| `PureGodelPairing.functional`、`agrees` | 原两分支 Gödel 配对的纯图、总唯一性及自然数 guard 下的原规格。 |
| `PureOmegaIteration.functional`、`iterates_of_graph` | 可定义总唯一后继算子的内部 ω 迭代，明确初值、定义域与后继方程。 |
| `PureTransitiveClosure.exists_closure`、`unique` | 任意源集合的最小传递闭包由内部并集迭代构造，最小性使用内部归纳。 |
| `PureSetStage.hierarchy_specification`、`PureFiniteUniverseStage.universe_axiom` | 内部幂集层级及其值域之并满足原有限层级与有限宇宙公理。 |
| `PureFiniteUniverseStage.hereditary_instance` | 遗传有限关系逐源项等价于传递闭包的有限性。 |
| `PureNaturalDifference.iteration_exists`、`functional`、`agrees` | 截断前驱作为有限序数的并集，提供原减法有限递推的实际存在性、唯一性及规格。 |
| `PureNaturalDifferenceStage` | 此前九个符号在同一扩张中实现并保持旧规格；后续四项见下表。 |

## 第二轮序型与有限序列：29 / 29 完成

| 证明入口 | 已核验成果 |
| --- | --- |
| `PureOrderSemantics`、`PureFiniteOrderTypes.natural_type_exists`、`natural_type_unique` | 原线序、极值及序同构桥接到内部良序坍缩；原最大元条件迫使序型属于内部 ω，任意原候选也由坍缩唯一性确定。 |
| `PureNaturalOrderType.functional`、`agrees` | 自然离散序型的纯图、任意参数总唯一性及原 guard 下的精确规格。 |
| `PureBoundedNaturalOrder.greatest_of_bounded`、`PureNaturalSubsetType.functional`、`agrees` | 有界自然数子集存在最大元并有有限序型；无界分支输出 ω，两分支完整满足原规格。 |
| `PureReplacement.mapping_exists`、`PureSequenceConcatenation.exists_concatenation`、`unique` | 当前纯公式的替换收集接口；内部和长度被前段和移位后段不相交地覆盖，给出唯一拼接图。 |
| `PureFlattenRecursion.accumulator_exists`、`PureSequenceFlatten.accumulator_finite_values`、`accumulator_unique` | 内部有限累积序列存在，各合法位置仍为有限序列；原递推方程唯一确定整个累积图与末值。 |
| `PureRoundTwoStage`、`PureRoundTwoSpecifications` | 四项完整原定义实例在同一实际扩张中成立，并保持旧函数规格和关系正文。该阶段累计 47 个函数、33 个关系；随后第三轮 30 个符号已全部完成。 |

本轮没有加入对象公理、外部标准性或外部良基性假设；后续全部支撑公理验证与裸 ZFC Rosser 合同已完成。

## 第三轮首批：递归语法识别与结构

| 模块 | 完成内容 |
| --- | --- |
| `Automation.PredicateExpansion` | 关系原子替换、模板与模型更换的语义对应，正出现正文的单调性。 |
| `PureLeastFixedPoint` | 实际纯公式的内部最小不动点图、存在唯一性与不动点方程。 |
| `PureSyntaxOperator`、`PureSyntaxFixedPoint` | 三个原语法识别正文的共同算子、集合界、元组单射性及三个实际切片图。 |
| `PureSyntaxStage`、`PureStructureStage` | 三个语法识别关系、非逻辑符号全集、结构谓词，在同一裸 ZFC 模型扩张中满足原定义。 |
| `PureRoundThreeSpecifications` | 保持第二轮既有规格。该阶段第三轮完成 5 / 30，累计 48 个函数、37 个关系；余下 25 个符号在后续批次完成。 |

原递归方程由最小不动点构造推出，未使用外部标准 ω、外部良基性或新增公理；全部模块进入默认构建。本批之后的完整公理验证及 Rosser 合同现也已完成。

## 第三轮第二批：相关语法、收集集合与分离规则

| 模块 | 完成内容 |
| --- | --- |
| `PureRelatedSyntaxOperator`、`PureRelatedSyntaxFixedPoint` | 带符号集参数的三个正递归识别关系；复用内部最小不动点、Kuratowski 查询图与集合界。 |
| `PureRelatedSyntaxStage` | 原递归正文的参数保持及整体模型装配，三个相关语法定义逐参数成立。 |
| `PureRelatedSyntaxSets` | 相关项码与公式码的内部 ω 界、纯分离、任意参数存在唯一性与原成员规格。 |
| `PureRelatedStage` | 六个新符号及其原定义，同一模型中的旧图保持、规格传输和分离规则正文。该阶段累计 50 个函数、41 个关系；余下 19 个符号在后续两批完成。 |

本批复用既有接口，没有重做 AST 解码或假定模型 ω 外部标准。本批之后的完整公理与 Rosser 合同装配现也已完成。

## 最后两轮收尾：第一轮九个公理集合

| 模块 | 完成内容 |
| --- | --- |
| `PureStructuralCodeBounds` | 实际配对、数码、字段列、结构节点的内部 ω 封闭性；原识别关系的自然数界。 |
| `PureLogicalSchemaSets` | 九种模式的原存在见证、良构性及成员条件，纯分离所得集合的存在唯一性与精确规格。 |
| `PureLogicalSchemaStage` | 七个命题公理集合、量词分配集合、等式自反集合的统一扩张；七项命题公理模式的完整源闭句。该阶段累计 59 个函数、41 个关系；最后 10 个符号在下一批完成。 |

`LogicalRuleEncoding` 的模式及生成步骤改用存在见证，真正的闭包规则保留全称量词；相关源句和 quotation 重建。修正不单独计数，后续已完成全部支撑公理与 Rosser 合同装配。

## 最后两轮收尾：第二轮十个符号，累计 110 / 110

| 模块 | 已核验成果 |
| --- | --- |
| `Automation.RelationalCongruence`、`Automation.PredicateCongruence` | 依赖覆盖下的解释翻译同余、关系赋值逐公式同余；无需展开大型实际纯图。 |
| `PureNaturalTuple`、`PureSyntaxTransform`、`PureFreeVariableOccurs`、`PureTransformStage` | 内部有界正递归图及原语法变换、自由变量出现定义；原递归方程在实际扩张中成立。 |
| `PureTotalCodeBounds`、`PureDependentSchemaSets`、`PureAllSchemaStage` | 三种剩余模式的纯图、存在唯一性和原成员规格；全部 12 个模式及三族完整源闭句。 |
| `PureLogicalClosure`、`PureLogicalStage` | 基集、逻辑公理最小闭包和公理码识别；完整原闭包、生成与识别公理。 |
| `PureValueOperator`、`PureValueFixedPoint`、`PureValueStage` | 载体与内部 ω 上的带参数共同不动点，四参数保持，两个实际纯图与原互递归求值方程。 |
| `PureCompletedStage` | 同一扩张保留全部实际图，求值定义、全部模式与逻辑公理码闭句同时成立。第三轮 30 / 30，累计 64 个函数、46 个关系，剩余符号为零。 |

没有新增对象公理、证明占位或外部标准性／良基性假设；全部模块进入默认构建。
后续已完成全部 119 条支撑公理及原 ZFC 公理像的统一验证、Rosser 句子真值对应与合同实例。

## 旧架构归档

<details>
<summary>旧架构记录（历史声明与路径，不能作为当前构建入口或完成状态）</summary>

以下内容保留历史记录，其中部分文件、声明和旧 Hilbert 接口已在重构中退役。

# 旧架构奖杯记录

本页是项目里程碑与可复用形式化资产的稳定展示出口。这里不建立重复的包装定理：
每一项都直接指向仓库中参与正常构建的真实 Lean 声明。

收录标准：

1. 声明具有明确的数学内容或可复用的证明工程价值。
2. 声明使用其实际需要的假设，不以更强前提换取临时闭合。
3. 声明所在依赖链不含 `sorry`，并通过项目的 `lake build`。
4. 基础设施与终局定理同等计入成果，不把大部分工作隐藏在单个终局名字后面。

截至 2026-08-15，本页所列 Rosser 依赖链已通过全仓 `lake build`，共 456 个构建任务。
这里的“无 `sorry`”表示该依赖链未引入 `sorryAx`；项目的可信计算边界仍包括 Lean
内核及仓库既有的 `native_decide` 使用。

## Lean 入口

```lean
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCRosserIncompleteness

#check YesMetaZFC.Logic.FirstOrder.FormalSystem.fs_zfc_rosser_incompleteness
#check YesMetaZFC.Logic.FirstOrder.FormalSystem.Rosser.fs_checked_hilbertized_proof_code_for
#check YesMetaZFC.Logic.FirstOrder.FormalSystem.GodelQuotation.fs_diagonal_lemma
```

## 终局里程碑

| 编号 | Lean 声明 | 形式化成果 | 源码 |
| --- | --- | --- | --- |
| ZFC-R01 | `fs_zfc_rosser_incompleteness` | 仅由内部 ZFC 支持理论的一致性，得到一个句子及其否定均不可由该理论 Hilbert 推导。全部内容在对象语法与 Hilbert 推导内完成。 | [ZFCRosserIncompleteness.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/InternalTheory/ZFCRosserIncompleteness.lean) |
| ZFC-R02 | `fs_zfc_rosser_independence_of_diagonal` | 将真实 quotation、Rosser 固定点、正负内部化与一致性装配为独立性结论。对象证明码和有限比较均封装在定理体内。 | [ZFCRosserIncompleteness.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/InternalTheory/ZFCRosserIncompleteness.lean) |
| CORE-R01 | `Rosser.independent_of_fixed_point_internalization` | 通用的纯 Hilbert Rosser 终局：固定点等价式加正负两个内部化蕴含及一致性即可推出双向不可证。 | [RosserFinite.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/RosserFinite.lean) |

终局定理的实际 Lean 类型为：

```lean
theorem fs_zfc_rosser_incompleteness
    (hConsistent :
      Derives.Consistent fs_zfc_support_theory []) :
    ∃ fixedPoint : SetFormula,
      Formula.Sentence fixedPoint ∧
        (¬ HilbertDerives fs_zfc_support_theory fixedPoint) ∧
        (¬ HilbertDerives fs_zfc_support_theory
          (Formula.neg fixedPoint))
```

这一定理没有把 proof code、replay trace、对象 verifier、模型或元层传输暴露为参数。

## 通用证明码内核

| 编号 | Lean 声明 | 形式化资产 | 复用边界 | 源码 |
| --- | --- | --- | --- | --- |
| CODE-01 | `Rosser.fs_checked_hilbertized_proof_code_for` | 将“代码 replay 成功且目标公式出现在最终证明状态中”封装为二元证明码关系。 | 参数化于任意带 Hilbert 理论枚举的理论。 | [CheckedCompleteness.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/CheckedCompleteness.lean) |
| CODE-02 | `Rosser.fs_checked_hilbertized_proof_code_for_sound` | 从 checked proof code 恢复 Hilbert 可推导性。 | 只消费 replay 的可靠性，不要求对象理论反射。 | [CheckedCompleteness.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/CheckedCompleteness.lean) |
| CODE-03 | `Rosser.fs_checked_hilbertized_proof_code_for_exists_of_derives` | 每个有限 Hilbert 推导都可编译为真实 checked proof code。 | 仅要求理论枚举和理论对 Hilbert 化闭合。 | [CheckedCompleteness.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/CheckedCompleteness.lean) |
| CODE-04 | `Rosser.fs_replay_raw_rows_nil_some_alignment` | 成功 replay 精确恢复规范解码行、最终 proof 与证书序列。 | 这是已完成的成功反演层；下游只调用，不再扩张。 | [RawAlignment.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/CheckedReplay/RawAlignment.lean) |
| CODE-05 | `Rosser.FSReplayCodeFailure`、`Rosser.fs_replay_code_failure_of_none` | 将总 replay 的 `none` 分解为证书解码失败或逐行 replay 失败。 | 只作为失败适配器的内部视图，不进入 Rosser 终局接口。 | [Failure.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/CheckedReplay/Failure.lean) |

这组接口形成可复用的往返边界：

```lean
HilbertDerives theory formula
  -> ∃ proofCode,
       fs_checked_hilbertized_proof_code_for
         enumeration proofCode formula

fs_checked_hilbertized_proof_code_for
    enumeration proofCode formula
  -> HilbertDerives theory
       (Formula.hilbertize SetSort.set formula)
```

## 对象证书系统

| 编号 | Lean 声明 | 形式化资产 | 复用边界 | 源码 |
| --- | --- | --- | --- | --- |
| CERT-01 | `ObjectCertificateVerifier` | 对象层理论证书 verifier 的最小合同，只规定公式合法性条件与证书条件。 | 与具体 ZFC 编码解耦，其他对象理论可以提供自己的证书条件实例。 | [CertifiedProofCodeEncoding.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/CertifiedProofCodeEncoding.lean) |
| CERT-02 | `fs_zfc_object_certificate_verifier` | ZFC 的闭合对象证书 verifier，统一覆盖有限公理表、分离模式和收集模式。 | 两个公理模式被放入证书检查层，不扩张 Rosser 终局假设。 | [ZFCObjectVerifier.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/InternalTheory/ZFCObjectVerifier.lean) |
| CERT-03 | `fs_zfc_support_raw_certified_code_condition_of_derives_at_quote` | 从 ZFC Hilbert 推导构造标准证明码，并在公式的真实 quotation 上证明对象层证书条件。 | Rosser 正向内部化的公共入口。 | [ZFCCheckedProofInternalization.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/InternalTheory/ZFCCheckedProofInternalization.lean) |
| CERT-04 | `fs_zfc_support_raw_certified_code_condition_neg_of_checked_not` | checked 二元关系不成立时，在对象理论中否定相同 numeral 与真实 quotation 上的证书条件。 | Rosser 负向内部化的公共入口；失败 trace 不向外泄漏。 | [ZFCCertifiedProofRelationRejection.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/InternalTheory/ZFCCertifiedProofRelationRejection.lean) |
| CERT-05 | `CertifiedProof.fs_zfc_support_raw_logical_certificate_condition_neg_of_failure` | 将逻辑证书检查失败统一转换为对象层否证。 | 失败适配器的逻辑公理出口，不建立新的 tag 反演层。 | [ZFCLogicalTailFailureAssembly.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/InternalTheory/ZFCLogicalTailFailureAssembly.lean) |

正负两个公共入口精确对齐同一个二元外部关系：

```lean
HilbertDerives fs_zfc_support_theory formula
  -> ∃ proofCode,
       Derives fs_zfc_support_raw_theory []
         (certified_code_condition proofCode (quote formula))

¬ fs_zfc_checked_hilbertized_proof_code_for proofCode formula
  -> Derives fs_zfc_support_raw_theory []
       (¬ certified_code_condition proofCode (quote formula))
```

上式使用数学形状省略了 fresh base、numeral 项及 quotation 等式；仓库中的 Lean
声明保留这些必要的语法参数。

## Gödel 编码与对角化

| 编号 | Lean 声明 | 形式化资产 | 复用边界 | 源码 |
| --- | --- | --- | --- | --- |
| QUOTE-01 | `GodelQuotation.fs_named_hilbert_tokens_decode_with_env_canonical_forall_open` | 在 token 新鲜性下，将规范 binder 正文打开为自由变量，并证明解码结果等于公式层 `openAt`。 | 为量词逻辑证书的正向解码与失败反演提供统一语法接口。 | [FormalSystemNamedTokenDecoderOpening.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/GodelQuotation/FormalSystemNamedTokenDecoderOpening.lean) |
| QUOTE-02 | `GodelQuotation.fs_diagonal_lemma` | 对任意扩展编码理论、可接受且只含指定代码变量的公式，生成闭句、真实 quotation 与目标理论内的 Hilbert 固定点。 | 与 ZFC 和 Rosser 谓词无关的通用内部对角引理。 | [Diagonal.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/GodelQuotation/Diagonal.lean) |
| QUOTE-03 | `fs_zfc_rosser_diagonal` | 将通用对角引理实例化到 ZFC Rosser 谓词，得到真实 quotation 对齐的 Rosser 句。 | 不增加模型、标准性或额外对象理论层。 | [ZFCRosser.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/InternalTheory/ZFCRosser.lean) |

## 对象有限算术与 Rosser 装配

| 编号 | Lean 声明 | 形式化资产 | 复用边界 | 源码 |
| --- | --- | --- | --- | --- |
| ARITH-01 | `fs_zfc_support_raw_rosser_natural_cut` | 对任意对象自然数和标准 numeral `q`，在对象理论内证明其落在 `≤ q` 或 `> q` 一侧。 | 只暴露二元成员关系，分离见证和归纳细节封装在模块内部。 | [ZFCRosserNaturalCut.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/InternalTheory/ZFCRosserNaturalCut.lean) |
| ARITH-02 | `fs_zfc_support_raw_certified_code_comparison_of_numeral_branches` | 一个正证明码加所有严格较小码的有限逐点否证，装配为对象层 Rosser 比较。 | 只消费有限逐点分支。 | [ZFCRosserFiniteAssembly.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/InternalTheory/ZFCRosserFiniteAssembly.lean) |
| ARITH-03 | `fs_zfc_support_raw_certified_code_comparison_neg_of_right_numeral` | 一个右侧证明码加其以下左侧代码的有限否证，推出 Rosser 比较的对象层否定。 | 为 Rosser 负向内部化提供有限分支终点。 | [ZFCRosserFiniteAssembly.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/InternalTheory/ZFCRosserFiniteAssembly.lean) |
| BRIDGE-01 | `fs_zfc_support_hilbert_derives_of_raw` | 将 raw 支持理论中的对象推导编译为 ZFC 支持理论中的 Hilbert 推导。 | 终局只通过这一方向提升，不暴露 raw 理论实现细节。 | [ZFCCheckedReplay.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/InternalTheory/ZFCCheckedReplay.lean) |

## Rosser 依赖链

```text
通用 checked proof code
  -> 成功 replay 对齐
  -> ZFC 对象证书 verifier
  -> quotation 上的正向内部化

checked 二元关系失败
  -> replay 失败视图
  -> 对象层证书条件否定
  -> 有限自然数切分与 Rosser 比较

通用内部对角引理
  -> ZFC Rosser 对角句
  -> 纯 Hilbert Rosser 终局
  -> fs_zfc_rosser_incompleteness
```

这条依赖链固定为“成功反演层 + 失败适配层”。`FSReplayCodeFailure` 和逻辑失败
payload 只在适配器内部消费；公开 Rosser 谓词及终局定理只使用二元证明码关系。

## 后续收录规则

新的奖杯条目应直接引用公开 Lean 声明及源码，不增加仅用于展示的 theorem 别名。
若成果依赖重要基础设施，应分别登记终局与基础设施，避免把可复用资产压缩成一句
“某定理已完成”。构建状态或可信边界发生变化时，应同步更新本页日期与审计说明。

</details>
