# 自然数证明证书编解码

当前提供支撑公理理论 `ProofT.ZFC.intrinsic_zfc_theory` 上的实际可计算入口：

```lean
intrinsic_zfc_nat_encode : IntrinsicClosedProofCertificate → Nat
intrinsic_zfc_nat_decode : Nat → Option IntrinsicClosedProofCertificate
intrinsic_zfc_nat_check : Nat → SetSentence → Bool
```

`intrinsic_zfc_nat_check_sound` 证明检查器接受的闭句具有原理论中的普通
`Derives` 推导。解码结果保存实际结论与类型正确的证书，重放覆盖全部六条核规则。
公理分支使用已有呈现的证书，不从输入接收理论成员证明。

`intrinsic_zfc_nat_decode_encode` 证明任意结构闭证书 `c` 满足
`intrinsic_zfc_nat_decode (intrinsic_zfc_nat_encode c) = some c`，恢复的是整个证书。
`intrinsic_zfc_nat_encode_injective` 因而保证编码单射。
`intrinsic_zfc_derives_iff_nat_certificate` 给出完整的宿主表示等价：

```lean
Derives intrinsic_zfc_theory [] φ ↔ ∃ n, intrinsic_zfc_nat_check n φ = true
```

编码沿既有证书递归，不通过经典选择从可证性命题抽取数据。统一替换按源上下文
枚举为有限项列，并证明还原后的函数与原替换相等；schema 的闭性证明通过证明无关性保留。

基础 ZFC 公理关系已有具体 `BaseAxiomPacket.presentation`，包含全部八条固定公理
和两个无界模式的正负表示。现已通过有限生成性证明，进一步完成与原支撑理论推导等价的
完整公理基表示 `ReducedAxiomPacket.presentation`。带标注整树检查的可靠性、完备性及
统一递归对象外壳和具体局部对象测试均已完成。`ReducedProofPresentation.presentation`
现提供支撑理论上的具体 `Delta1ProofPresentation`；`ReducedRosser` 进一步完成具体固定点
及仅假定一致性的不完备实例。裸 ZFC 的支撑消去尚未完成。`none` 只表示该输入不是此格式的
合法闭证明，不能推出目标闭句不可证。

## 当前 quotation 与公理模式边界

当前核保留十一种公式构造子。旧 `QuineEncoding.quote` 先做 Hilbert 化，满足
`quote (hilbertize φ) = quote φ`，但自然数检查器仍要求实际结论 AST 完全相等。
`ZFC.SchemaQuotationAudit` 已证明任意参数与正文的分离、收集模式具有这种冲突：
同一个公理证明码接受原实例，拒绝其不同的 Hilbert 化实例。一般相容性定理据此
排除在一致理论内使用旧码为当前检查器建立统一正负表示；这不是 schema 不可表示。
替换模式也已证明与其 Hilbert 化 AST 不同，但未被添加到现有 ZFC 公理证书中。

`IntrinsicQuotation.quote` 直接把 `SyntaxEncode.formula` 的有限树嵌入现有对象项。
节点为 `S(pair(tag, fields))`，字段采用原结构列表的 nil/cons 编码。该编码保留
全部构造子，且有 `unquote_quote`、`quote_injective`。`quote_evaluate` 与 `quote_ne`
在原 `CertificateCore` 上分别证明对象求值及任意两个不同公式码的不等。
这些对象推导不要求理论一致性，也不增加公理。数值求值仅用于符号化证明，
正常 quotation 保留紧凑结构项，不展开巨大的一元自然数。

公共 `Delta1ProofPresentation` 和 `RosserPresentation` 已使用新码及配套否定码。
旧 `IntrinsicSchemaCertificate`、`IntrinsicVerifier`、`IntrinsicGraph` 仍使用旧
Hilbert 结构格式；这些定义不能直接作为新表示的实例。

| 模式检查阶段 | 当前状态 |
| --- | --- |
| 模式标签、字段数量、参数叶子，正文保留为任意原始树 | `SchemaEnvelope` 的统一 Delta0 图及正负对象证明已完成；已连接实际分离/收集解码器 |
| 正文项构造与束缚变量作用域 | `SchemaTerm` 直接表示 `ProjectDecode.term` 的成功/失败，统一 Delta0 图及正负对象证明已完成 |
| 整个正文的递归识别与量词下作用域 | `SchemaObjectGraph.Body.condition` 为固定 Delta0 公式；`SchemaBodyDerives` 从实际检查器的 true/false 给出正负 Derives，数值码与紧凑树码均已连接 |
| 原始自然数数据包到对象树码 | `NatPacketLink` 已直接表示实际 `NatPacket.decode`，统一 Delta0 图及正负 Derives 完成；覆盖非法包与错误候选树 |
| 正文重命名 | `SchemaObjectGraph.Rename.condition` 为固定 Delta0 公式；`SchemaRenameDerives` 从实际 run 的正确结果或任意错误候选输出给出正负 Derives，六个实际位置已接入 |
| 固定模式模板构造 | `SchemaTemplate` 接入六处实际重命名并逐节点恢复三类核心；`SchemaTemplateDerives` 已给出同一带标签 Delta0 装配图及正负推导 |
| 参数全称闭合 | `SchemaClosure` 已用固定两条规则表示任意层数，并精确连接实际三类模式闭句；正负 Derives 完成 |
| 参数重命名表生成 | `SchemaTable` 固定八条规则生成六个实际位置的表，任意参数数目，正负 Derives 完成 |
| 模式中间槽位的对象连接 | `SchemaJoin` 固定四元图量化三张表、三个正文及核心，正负 Derives 完成；输入输出为 Project 原始树码 |
| 内核 quotation 与完整模式证书连接 | `KernelQuotation`、`SchemaKernelJoin`、`SchemaPacket` 已完成转换与有界对象连接，公开二元包码/结论码图 |
| 已解析实例的结论与任意目标闭句精确比较 | `SchemaConclusion.positive`、`negative` 已在原支撑理论内证明，覆盖分离、收集、替换 |
| 任意原始 schema 证书的统一正负表示 | `SchemaPacket.actual_positive_number`、`actual_negative` 已对齐原公理解码器的模式分支，包含全部失败输入 |
| 全部 ZFC 基础公理的统一正负表示 | `BaseAxiomPacket.presentation` 已合并八条固定公理和两类模式；接受恰好对应原公理像 |
| 参数化支撑公理的证书合法性 | `SupportParameter` 已表示全部 11 类原分支的接受、拒绝，包含完整内核项与 indexed 外壳 |
| 参数化支撑公理的计算层装配 | `SupportRealization` 已连接 11 类固定模板代入、全称闭合、实际内核结论、quotation 及内层参数包 |
| 完整等价公理基 | `ReducedAxiomPacket.presentation` 合并基础公理与 119 条支撑闭句，实际包检查和正负对象表示完成；普通推导与原理论等价 |
| 完整内核公式识别 | `ObjectFormulaSyntax.checked_decode` 在所有自然数上精确对应 quotation / AST 解码；固定 Delta0 公式及正负推导完成 |
| 完整证明树的计算检查 | `ProofTreeCode` 保存每个节点的自由上下文长度和实际结论，六条核规则的局部重放、整树可靠性及完备性完成；`ReducedProofTree` 已连接原理论 |
| 当前核语法变换 | `ObjectSyntaxTransform` 的 28 条规则统一表示自由加强、首变量抽象、首束缚变量实例化及同时自由代入；正负推导与实际核操作已连接 |
| 全部逻辑公理 | `ObjectLogicalAxiom` 的 27 类有限模式已有可靠性、接受完备性及全自然数实际解码规格 |
| 具体节点 LocalTest | `ObjectProofNode` 的六类规范模式及 `ReducedProofPresentation.nodeTest` 已完成；与实际局部核检查及全部证书编码连接 |
| 完整证明树的对象表示 | `ObjectProofRow`、`ObjectProofNode.ofNodeTest` 装配递归图与根 quotation；`ReducedProofPresentation.presentation` 为原支撑理论上的具体完整实例 |

`CodePattern` 将有限构造模式编译为后继、配数及有界量词公式。
`bounded_exists_numeral_neg` 从每个标准位置的否定推出整个有界存在的否定，
因而两个新识别器的负向证明排除了界内任意对象见证，而非只处理宿主已解析见证。
参数可以是任意自然数；正文项索引由输入的作用域项界定，没有固定上限。
新证明在 `IntrinsicQuotation.tree input` 与对应数值码上均有出口。这里的树码
是 `treeValue`，不是传输层的 `NatPacket.encode input`，不能互相代换。

旧 `IntrinsicForallPrefix` 的轨迹端点是 `trace[0] = closed`、`trace[n] = core`。
局部等式现修正为 `trace[i] = all_code(trace[i+1])`，与逐层剥离外层量词一致；
该修正仍属于旧码图，不声称已经完成新码的全称闭合表示。

`SchemaBody.decode_spec` 的归纳覆盖全部十二种 Project 构造子，同时得到自由闭性和
精确重编码；因此实际模式解码器后置的 `FreeClosed` 检查不会改变接受集。
`SchemaRename` 的源作用域是有限表长度，目标索引逐项检查。穿过量词时使用
`0 :: table.map Nat.succ`，保持新束缚变量不动，且同一交换律适用于任意嵌套深度。
`run_eq_some_iff` 与 `run_ne_some_iff` 刻画任意原始输入及任意候选输出，
`run_intrinsic`、`run_quotation` 直接连接当前内核 AST 与新码，不经过旧 Hilbert 化引用。
在这些数据层定理之上，`SchemaBodyDerives` 与 `SchemaRenameDerives` 已完成统一对象表示：

| 输入判准 | `intrinsic_zfc_theory` 中的普通推导 |
| --- | --- |
| `SchemaBody.check depth input = true` | `SchemaObjectGraph.Body.condition depthCode inputCode` |
| `SchemaBody.check depth input = false` | 上述同一公式的否定 |
| `SchemaRename.run target table input = some output` | `SchemaObjectGraph.Rename.condition targetCode tableCode inputCode outputCode` |
| `SchemaRename.run target table input ≠ some output` | 上述同一公式的否定，包含执行成功但输出不匹配 |

公共 `positive`、`negative` 使用标准数值码；`positive_at_tree`、`negative_at_tree`
使用 `IntrinsicQuotation.tree` 和有限 numeral 表的结构列表码。这里仍不是
`NatPacket.encode` 传输包，也没有把树码与当前内核 AST 的 quotation 偷换为同一个码。

两套公式均由固定规则表生成。正文有 13 条规则；重命名有 21 条规则，分别处理
查表、cutoff 下索引提升、项、完整正文、整表目标合法性及最终运行。公式形如
`∃ trace ∈ 𝒫(ω), root ∈ trace ∧ ∀ row ∈ trace, step(row, trace)`；每条局部规则的
参数均在 `S(row)` 内有界量化。`condition_delta0` 是当前带已有 `ω`、幂集、配数
等项符号的扩展集合论语言中的分类，不声称已完成向纯成员语言裸 ZFC 的消去。

通用证明位于 `Automation.ObjectFiniteSet`、`ObjectTrace`、`ObjectHorn*`。
正向由实际递归结果组装有限闭合行集，再证明其为对象轨迹。负向在每个标准根行
上穷尽有界规则赋值，用头码、守卫及递归失败前提排除该行。拒绝证书的递归按原树
大小、表长或 cutoff 严格下降；对象轨迹本身可以是任意见证，不假定标准、有限或
已被宿主解析。不引入规则公理、解释符号、语法深度上限或自定义证明核。

实际模式表如下；尾部的 `j` 遍历 `0 ≤ j < n`，不设置参数上限。

| 正文位置 | 源深度 | 目标深度 | 索引表 |
| --- | --- | --- | --- |
| 分离 | `n+1` | `n+3` | `[0] ++ [j+3]` |
| 收集前件 | `n+2` | `n+3` | `[0,1] ++ [j+3]` |
| 收集像集 | `n+2` | `n+4` | `[0,1] ++ [j+4]` |
| 替换第一输出 | `n+2` | `n+3` | `[1,2] ++ [j+3]` |
| 替换第二输出 | `n+2` | `n+3` | `[0,2] ++ [j+3]` |
| 替换像集 | `n+2` | `n+4` | `[1,0] ++ [j+4]` |

模式内部中间码现已由下述 `SchemaJoin` 有界量化并连接；后续仍需完成 Project 树码到内核 quotation 的转换，
再与模式外壳及已完成的传输包连接组合。负向证明必须覆盖非法标签、参数数目、作用域以及任意错误输出；
不得通过预先假设正文合法或把已计算结论直接作为输入来省略这些分支。

## 固定模式模板

`SchemaTemplate` 使用 `Automation.ObjectTreeTemplate` 的固定树模板编译器，槽位里
保存已经重命名的正文码。模板标签独立于原始公理证书标签，不改变 ZFC 公理呈现。

| 模板标签 | 模式 | 使用的正文槽位 | 产物 |
| --- | --- | --- | --- |
| 0 | 分离 | 分离正文 | `separationCore` 的 Project 编码 |
| 1 | 收集 | 前件、像集 | `collectionCore` 的 Project 编码 |
| 2 | 替换 | 第一输出、第二输出、像集 | `replacementCore` 的 Project 编码 |

`separation_core`、`collection_core`、`replacement_core` 对任意参数数目证明精确树等式，
保留所有成员索引、有界量词展开和替换唯一性中的外延相等原子（标签 3）。
`run` 从原始正文执行六个既有重命名位置，再填槽；`run_isSome` 证明其接受集
恰好是源作用域的 `SchemaBody.check`。非法正文不会被模板装配修复。

`SchemaTemplate.template` 是五个固定 free 槽位中的一个公式：模板种类、三个正文码、
候选输出码。`template_apply` 证明其类型化实例化等于公开 `condition`；
`template_delta0` 和 `condition_delta0` 给出当前扩展语言中的 Delta0 分类。
各分支只以既有后继和配数构造固定项，再与候选输出码比较，未把宿主计算出的
完整结论嵌入公式，也没有增加模板解释公理。

`positive`、`negative` 允许槽位和候选输出是任意标准自然数；`positive_at_tree`、
`negative_at_tree` 使用紧凑原始树码，错误输出允许畸形树；`unknown_tag_negative`
在任意闭项槽位上拒绝未知标签。三个 `*_positive` 直接提供实际模式核心的对象推导。
所有接口使用普通 `Derives`，不需要一致性或语法深度界。

此处完成的是固定装配图。模板自身不检查正文合法性，也不执行对象层重命名；
六处重命名到模板的宿主 `run` 已连接；后面的 `SchemaJoin` 进一步完成模式内部的对象存在连接。
参数全称闭合和自然数传输包连接已在下一节完成独立对象图；新内核 quotation
转换及包、模式外壳对统一模式图的完整连接已在后续 `SchemaPacket` 层完成。此阶段的树码仍为
`IntrinsicQuotation.tree` / `treeValue`，不是 `NatPacket.encode`，也不是直接把
Project 树码认作当前内核 AST 的 quotation。替换仍只提供模式接口。

## 参数全称闭合与传输包对象连接

`SchemaClosure.condition count core closed` 使用 `ObjectUnaryIteration` 的两条固定规则：
零层返回核心码；后继层在上一步结果外添加一个标签 9 的全称节点。参数层数本身是
对象输入，公式长度不随它增长。`encode_forallClosure` 证明其与实际 Project 全称闭合
逐节点交换，三个 `run_*` 恢复三类模式的实际闭句编码。数值正负接口允许任意自然数
核心码和候选输出；紧凑树码接口允许任意原始树。负向按参数层数下降，排除任意对象轨迹。

`NatPacketCanonical.decode_eq_some_iff` 给出精确规格：
`NatPacket.decode packet = some input ↔ NatPacket.encode input = packet`。
证明分别反演字节读取、规范 varint 读取、树和子树列表读取，不额外插入一个规范性
检查，也不改变原解码器的接受集。

`NatPacketLink.condition packet treeCode` 是一个固定二元 Delta0 模板。其十条规则
分为以下六个辅助关系，全部编译为既有对象后继、配数、成员关系及有界轨迹公式。

| 行标签 | 数值含义 |
| --- | --- |
| 0 | `output = digit + 128 * tail`，且 `digit < 128` |
| 1 | `output = digit + 256 * tail`，且 `digit < 256` |
| 2 | 一个规范 varint 的字节前缀与任意尾数拼接 |
| 3 | 一棵任意有限树的先序字节前缀与尾数拼接 |
| 4 | 指定长度的子树列表前缀与尾数拼接 |
| 5 | 添加版本字节 1，并固定最高位终止标记为 1 |

前缀运算的所有中间标准数均已证明落在当前行码的后继界内。正向生成有限闭合轨迹；
负向依次按进位尾数、varint 数值、树或列表大小下降，并在标准候选树码处排除任意
对象轨迹。既不假定对象轨迹标准或已解析，也不新增字节运算或解释器公理。

公开 `positive` / `positive_at_tree` 直接接受实际 `decode = some input`；
`negative` / `negative_at_tree` 接受实际 `decode ≠ some input`，覆盖全部非法原始包，
也覆盖成功包给出另一棵候选树的情况。输入码确实是 `NatPacket` 的版本一数值，
输出码是 `treeValue` / `IntrinsicQuotation.tree`，没有把两种编码认作同一个自然数。
`proof_packet` 连接现有自然数证明解码器的最外层；`schemaRun` 从正文包依次运行
解析、重命名、固定模板和参数闭合，并对三类模式给出通用精确结果定理。

两层均提供固定 `FormulaTemplate` 和 Delta0 证明；分类仍位于具有既有 `ω`、幂集、
后继、配数项的扩展集合论语言。独立阶段的表示已经完成；模式内部的表生成与中间码连接见下一节。
包、模式外壳及 Project 树码到当前内核 quotation 的完整连接见后续 `SchemaPacket` 层。
不把宿主 `schemaRun` 的组合定理算作已经闭合的单一对象检查公式，也不宣称已得到裸 ZFC Rosser 实例。


## 重命名表生成与模式中间码统一连接

`Automation.ObjectRangeTable` 用两条递归规则生成 `[start, …, start+n-1]`，
再由固定描述表附加短前缀。`ZFC.SchemaTable` 的六个描述恰好对应实际 `Site.mapping`；
包括递归器在内总计八条规则，与参数数目无关。`positive` 给出实际生成表的对象推导，
`negative` 排除任意错误自然数表码，包含非列表码。

中间正文码不能预先假定为树，因此 `SchemaRenameNumeric` 将既有递归拒绝证书
扩展为 `run_number_reject` 和 `negative_number`：
`(SchemaRename.run target table input).map treeValue ≠ some candidate` 即得到对象否定。
其候选值为任意自然数；递归只沿已给原始输入树严格下降，未增加核规则或对象公理。

`SchemaJoin.template` 是固定四元对象公式 `J(kind,n,input,output)`。
每个分支在对象层真实量化七个见证：三张表、三个重命名正文以及模式核心。
分离复用同一个位置三次，收集复用第二个位置；这使各分支共用同一个固定矩阵。
矩阵依次连接表生成、重命名、固定模板与参数全称闭合；正文的作用域检查由
实际重命名器的成功规格承载，不作为额外前提传入。

所有见证共用界 `S(godel_pair(B(n), output))`，其中
`B(n) = (n+8)^(16^(n+2))`。`ObjectCodeBounds.list_bound` 证明长度和元素受界列表的
结构码上界；三张实际表都落在 `B(n)` 以下。实际重命名正文是模式核心的子树，
核心不超过参数闭合后的结论码，因此其余四个见证也落在同一个界内。
界仅是充分的见证界，不是语法深度护栏，且不是额外公开槽位。
幂、后继和配数都是已有支撑语言中的项；没有增加计算解释公理。

`SchemaJoin.positive`、`negative` 使用普通 `Derives intrinsic_zfc_theory []`，
直接消费实际 `SchemaClosure.run` 经 `treeValue` 映射的成功或失败等式。
正向在对象层引入七个见证；负向先排除错误表，随后排除错误重命名码、错误模板
和错误闭合码，最后由有限 numeral 成员反演消去任意对象见证。
不要求见证预先为标准项、列表或树，也不要求一致性、可靠性或额外表示合同。
`positive_at_tree`、`negative_at_tree` 提供同一图的紧凑树项接口。
`separation_positive`、`collection_positive`、`replacement_positive` 直接连接
仓库实际三类 Project 模式闭句。未知标签也有任意闭项上的否定接口。

此时正文至 Project 模式闭句已经有单一对象图的正负表示，不再只是宿主流程组合。
`template_delta0` 仍指既有扩展支撑语言中的 Delta0，而非纯隶属语言的分类。
包自然数、Project 树码与内核 quotation 保持区分；三者的完整对象连接见下一节。
整个证明检查器的对象图仍待接入；完整等价公理基见后文。替换仍为单独模式接口，
不改变现有 ZFC 的分离与收集呈现。

## 模式外壳、传输包与内核 quotation 的完整连接

`Automation.ObjectProjectQuotation` 使用固定十二条规则转换 Project 树：成员关系
和子集关系在目标节点中分别增加当前 `RelationSymbol.membership`、`subset` 字段，
等号与十一种内核公式构造子保持精确区别。原子项保持原树，作用域和原子字段数
由前级模式正文识别保证；转换器本身不充当正文合法性检查器。
`KernelQuotation.project_formula_code` 对任意自由闭 Project 公式证明转换等于
`SyntaxEncode.formula (project_formula ...)`，整个流程不经过旧 Hilbert quotation。
`ObjectProjectQuotation.positive`、`negative` 编译有限接受、拒绝证书为普通推导，
负向允许输出是任意自然数，而不只是一棵已给树的码。

`SchemaKernelJoin.condition kind n input output` 在 `S(output)` 内量化 Project 闭句码，
连接上一节的 `SchemaJoin.condition` 与 quotation 转换图。`run_le` 证明成功转换的
输入码不超过输出码，因此该界是对所有成功输入证明出来的充分界。
三类 `*_decode` 定理对全部原始正文证明结果等于实际类型化 schema 解码器和原闭句构造，
包括非法正文。`SchemaKernelInstances` 提供三类真实模式的紧凑 quotation 接口。

最外层 `SchemaPacket.template` 为固定二元公式 `P(packet,output)`。它只含原 ZFC
模式标签 8（分离）与 9（收集）两个分支，每个分支在 `S(B(packet))` 内量化
原始树码、参数数目和正文码。这里仍使用既有项
`B(packet) = (packet+8)^(16^(packet+2))`：`ObjectRawTreeBounds.packet_bound`
按树/列表结构成本、实际 token 长度和数值证明原树码的上界；外壳中的参数和正文
不超过原树码。这不是额外格式上限或公开的见证界参数。

外层三个中间码、内核连接的一个 Project 中间码、模式连接的七个中间码均已在
对象公式内隐藏。每一层仍使用原有固定轨迹图。负向先处理任意包/原树码候选，
再排除错误外壳，继而使用模式和 quotation 负向推导。`ObjectPacket.negative_number`
额外证明非树、非列表自然数也不可能通过传输图，因此不能通过畸形中间数逃逸。

独立规格 `SchemaPacket.actual` 直接调用原 `zfc_base_axiom_decode`，筛选其既有
分离、收集证书，再用原模式闭句与当前 `SyntaxEncode` 编码。
`SchemaPacket.run_eq_actual` 对所有包自然数证明新流程与此规格相等。
`actual_positive_number` 和 `actual_negative` 在任意自然数输入/输出上分别给出
同一个 `P` 与其否定的普通 `Derives intrinsic_zfc_theory []`；`positive_at_tree`、
`negative_at_tree` 允许紧凑树项，实际分离/收集端点直接使用当前 `IntrinsicQuotation.quote`。
这些接口不假设对象理论一致性、标准性、可靠性或另一个表示合同。

`template_delta0` 仍是在既有扩展支撑语言中的分类（含 ω、幂集、配数与自然数幂项）。
这里完成的是支撑理论上的 ZFC 模式证书分支；固定公理已在下一节并入。
完整等价公理基、证明图及具体固定点已在后续各节完成；裸 ZFC 的消去/传输仍是后续工作。

## 完整 ZFC 基础公理的具体表示

`BaseAxiomPacket.run packet` 直接运行 `NatPacket.decode` 和原 `zfc_base_axiom_decode`，
再将证书指定的实际闭句编码为当前 `SyntaxEncode.formula`。它不筛掉固定公理，
也不使用旧 Hilbert quotation。`AxiomCanonical` 证明任何成功基础证书重新编码后
恢复原始输入；`decode_eq_some_iff` 进一步得到成功自然数包恰好等于该证书的规范编码。
所有模式参数数目均无固定上限。

对象端的 `BaseAxiomPacket.template` 是一个固定二元公式，由八条固定公理的
`ObjectFiniteTable` 与已有 `SchemaPacket` 取析取构成。固定表保留紧凑的树常量，
不展开巨大数码。通用表允许重复键；否定证明要求排除每一匹配行，因此不依赖
隐含的键唯一性或首项查找语义。

| 规格或检查结果 | 已证明出口 |
| --- | --- |
| `(run packet).map treeValue = some output` | `positive_number` 给出同一对象图的普通推导 |
| `(run packet).map treeValue ≠ some output` | `negative` 给出其否定，候选可为任意自然数 |
| `run packet = some outputTree` 或其失败 | `positive_at_tree`、`negative_at_tree` 使用紧凑树项 |
| `checked packet formula = true` | 原 ZFC 公理像成员关系，以及当前 quotation 上的正向对象推导 |
| `checked packet formula = false` | 同一个公式在当前 quotation 上的否定推导 |
| 原 ZFC 公理像包含 `formula` | 存在一个检查器接受的实际自然数包 |

`checked` 复用 `intrinsic_zfc_base_axiom_presentation.check` 的精确内核闭句比较。
`checked_run` 证明该 Bool 检查恰好等于独立规格输出对应内核树。
`BaseAxiomPacket.presentation` 已将全部字段填入公共
`Delta1AxiomPresentation intrinsic_zfc_theory intrinsic_zfc_axiom_theory`，并导出同一
公式的 Sigma1、Pi1 分类。这里的 Delta0 分类仍使用扩展支撑语言；推导所在理论与
所表示的公理集合由两个类型参数明确区分。该实例针对公理成员关系，尚不是针对
演绎闭包的 `Delta1ProofPresentation`。

原 `intrinsic_proof_axiom_decode` 除了固定公理，还包含携带上下文和一至四个实际项的
参数化分离族。下文保留其证书合法性表示及公理装配、闭合的计算层交换定理。
进一步的有限生成性证明允许改用推导等价的有限支撑基，从而完成当前公理对象表示。
这并不把有限分支表当作原无限参数证书关系的精确表示。其后连接逻辑公理、全部核规则
与完整证明树；这些连接及固定点现已完成，裸 ZFC 传输仍待完成。

## 参数化支撑公理的证书识别

`SyntaxCanonical` 对当前类型安全内核项证明成功解码后重新编码精确恢复原树。
它覆盖 `SyntaxDecode.functionSymbols` 中全部 76 个符号及签名要求的实际元数，
自由变量与束缚变量分别在各自上下文中检查。此层直接使用 `SyntaxEncode.term`，
不经过旧 Project 正文项或 Hilbert quotation。

`SyntaxParameters` 保留原 `AxiomPresentation.indexed` 的数据形状：外层为
`N(0; L(freeCount), spine)`，每个项为 `N(0; term, rest)`，末尾必须为 `L(0)`。
参数项的束缚上下文为空，自由上下文由外层叶子决定。`decode_encode` 与
`encode_of_decode` 分别给出类型化数据往返和原始输入规范性；通用接口支持任意项数。

`ObjectTermSyntax` 共用固定 83 条 Horn 规则：两条变量规则、76 条函数规则、
两条函数实参列规则、两条 indexed 项链规则和一条上下文外壳规则。全部规则变量均在
头部出现，沿用已有对象证书的内部数值界，不给公共接口增加上下文或项深度限制。
`termTemplate` 是束缚长度、自由长度、原始项码的三元公式；`parameterTemplate`
是项数、原始外壳码的二元公式。两者均有 Delta0 分类和正负普通 `Derives`。

`SupportParameters.actual` 直接运行各族原解码器的参数分支；`actual_eq_decode`
对任意原始树证明其 Bool 结果等于 `SyntaxParameters.decode` 的成功标志，覆盖拒绝输入。

| 公理族 | 原证书中项的顺序 |
| --- | --- |
| domain、range、converse | relation |
| cartesianProduct | left、right |
| composition | first、second |
| identity、inductiveCore | source |
| mappingCollection | source、target |
| indexOrder | sourceRelation、sourceCarrier、targetRelation、targetCarrier |
| powerSetBijection | natural |
| symmetricDifference | left、right |

`ZFC.SupportParameter.positive`、`negative` 直接接受上述实际 Bool 结果，在原
`intrinsic_zfc_theory` 内给出数值树码上的普通推导；对应 `_at_tree` 接口使用紧凑树项。
`encoded_positive` 覆盖任意类型正确的参数，无额外表示合同。各族按其项数复用同一
合法性公式；它尚未区分相同项数的不同公理结论，因此还不是这些公理的完整表示。

## 参数代入与支撑公理装配

`SyntaxSubstitution` 在当前内核原始树上定义项、公式代入。进入量词时提升替换项中的
束缚变量索引，保留最新绑定变量；`formula_substitute` 对任意源、目标上下文和类型正确
替换证明该算法与内核 `Formula.substituteMapped` 相同。项参数可以包含当前内核的任意
函数构造，不限于变量或常量。通用项重命名与代入复合定理保证参数在固定谓词内部的
绑定操作不产生变量捕获。

`SyntaxInstantiation` 从有限项列取得每个模板槽位，`instantiate_encode` 将原始码代入
连接到类型安全的 `substituteFree`。`SyntaxSubstitution.abstractTop` 把最新自由参数
转为束缚变量；`close_encode` 对任意自由上下文证明反复抽象、加全称量词得到的原始码
恰好编码 `Formula.forall_close`。此处必须执行内核自由变量抽象，不能仅在树外添加量词。

`SupportAssembly.template` 为上述 11 类公理分别固定完整开放分离公理，槽位数由
`Kind.arity` 决定。`SupportTemplate` 中的 `instantiate_eq` 证明任意实际项代入后精确
恢复原族 `separation_open_axiom`；`close_instantiate` 进一步恢复 `separation_axiom`。
上下文长度和项深度无固定上限；各族共有的分离外壳只需使用同一套代入交换律。

| 接口 | 已证明的连接 |
| --- | --- |
| `SupportConclusion.actual` | 直接读取各族原解码器及原公理呈现的实际闭句 |
| `SupportConclusion.actual_eq_decode` | 对所有原始输入，参数解码所得公理闭句与该实际结果相同，包含失败分支 |
| `SupportConclusion.sentence_derives` | 任意装配公理在对应原族理论中有普通 Hilbert 推导 |
| `SupportRealization.assemble_eq`、`assemble_quote` | 固定模板的原始码代入、闭合逐节点等于实际内核编码及当前 quotation |
| `SupportRealization.run_eq_actual`、`run_sound` | 任意成功输入精确产生对应原理论中可推导闭句的编码，拒绝输入也与原解码器一致 |
| `SupportRealization.packet_eq_actual`、`packet_encode` | 版本一包承载内层参数外壳，经装配得到原公理的同一内核闭句码 |

以上结果是原参数装配算法的计算层定义与交换定理，尚未给出该关系的统一对象公式和
正负 `Derives`。已有 `SupportParameter` 的正负表示仍仅识别证书合法性。
`SupportRealization.packet` 只包装内层参数外壳，尚未包含原 `intrinsic_proof_axiom_decode`
全部外层理论并路径。当前主线改用下述已经证明推导等价的有限公理基，因而这些旧格式
兼容工作不再阻塞支撑理论上的 Rosser 实例。当前 Delta0 分类仍属于已有扩展支撑语言，
尚不意味着裸 ZFC 完成。

## 完整等价公理基的对象表示

对每类参数公理，令 `closedTemplate kind` 为固定开放模板的全称闭包。
`SupportAssembly.sentence_of_closedTemplate` 在任意理论中证明：只要该闭模板可推导，
任意自由上下文、任意复杂项参数对应的原公理闭句就可推导。证明依次使用既有
`forall_close_elim`、类型安全项代入交换律和 `forall_close_of_derives`，不添加公理。

`FiniteAxiomBasis` 同时记录基中每个闭句是原公理，以及原理论的每个公理均可由该基
推导。其 `union`、`insert` 沿理论组合保持这两项性质；`SupportAxiomBasis` 逐层连接
完整原支撑理论。结构相等去重后，`ReducedAxioms.basis` 含 119 条闭句。

令 `T := intrinsic_zfc_theory`，`B := ReducedAxioms.theory`。已经证明：

```lean
B = Theory.union intrinsic_zfc_axiom_theory ReducedAxioms.basis.theory
-- ReducedAxioms.subset：B 中每个公理都属于 T。
-- ReducedAxioms.derives_iff：任意自由上下文和局部上下文。
Derives B Γ φ ↔ Derives T Γ φ
```

这里是推导等价，公理成员关系不同。原参数公理在 `B` 中通过普通推导展开，不再要求
它们都作为独立公理行进入检查器。其证明码格式也与原完整 union 证书分别命名。

`ObjectFiniteAxioms.presentation` 将任意有限闭句表编译为精确成员检查器和固定二元
Delta0 对象公式，正负推导使用当前 `IntrinsicQuotation.quote`。
`Delta1AxiomPresentation.union` 合并已有公理表示，接受时选择成功分支，拒绝时同时
排除全部分支。`ReducedAxioms.presentation` 因而合并原基础公理图与整个有限支撑表。

`ReducedAxiomPacket` 另行实现实际包解码，不以对象公式的真假定义检查器：

| 树格式 | 公理分支 |
| --- | --- |
| 原标签 0–7 的叶子 | 八条基础固定公理 |
| 原标签 8、9 的参数与正文外壳 | 分离与收集模式 |
| `N(10; L(index))` | 有限支撑公理基的有效索引 |
| 其他格式、越界索引、非法版本一包 | 拒绝 |

标签 10 在这个新公理入口中是有限基索引，不是替换模式，也不修改原基础解码器的
标签约定。外层仍使用版本一 `NatPacket`。`tree_roundtrip`、`tree_canonical`、
`decode_encode`、`decode_eq_some_iff` 给出往返与规范性；`checked_agrees` 对任意自然数包
和候选闭句证明实际解码检查与统一对象表示的检查器相同。

最终具体接口为：

```lean
ReducedAxiomPacket.presentation :
  Delta1AxiomPresentation intrinsic_zfc_theory ReducedAxioms.theory
```

所有字段均已填入：同一个二元公式、Delta0 分类、可计算检查、可靠性、完备性和普通
正负推导。非法包、错误公理结论和越界有限索引均在其拒绝范围内；表示证明不以一致性
为前提。该分类仍在既有扩展支撑语言中成立。

完整证明树已通过以下接口传回原支撑理论：

```lean
ReducedAxioms.liftProofPresentation :
  Delta1ProofPresentation intrinsic_zfc_theory ReducedAxioms.theory →
  Delta1ProofPresentation intrinsic_zfc_theory intrinsic_zfc_theory
```

传输保持同一检查器、对象公式和正负推导，只利用已经证明的推导等价性转换可靠性与
完备性。完整证明树表示和支撑理论上的具体 Rosser 固定点及不完备终局现均已完成。

## 带标注证明树与递归对象图

`ProofTreeCode` 为精简公理基新增独立的自然数证明格式；不替换已有版本一数据包。
每个节点为 `ObjectHorn.nodeValue tag fields`，前两项总是自由上下文长度及
`treeValue (SyntaxEncode.formula conclusion)`。其余字段如下：

| 标签 | 规则 | 额外字段 |
| --- | --- | --- |
| 0 | 逻辑公理 | 当前逻辑公理证书的结构树数值码 |
| 1 | 理论公理 | `ReducedAxiomPacket` 的自然数传输包 |
| 2 | MP | 前件证明码、蕴含证明码 |
| 3 | 全称概括 | 子证明码 |
| 4 | 自由变量加强 | 子证明码 |
| 5 | 自由变量代入 | 源上下文长度、替换项列的结构列表数值码、子证明码 |

自由上下文长度和子证明码字段直接存放自然数，不再包成 `leaf`。
结论 AST 使用结构 quotation 数值码；理论公理字段使用版本一传输包。这两类码
通过各自的实际解码器读取，不能互换。

`IntrinsicQuotation.decodeTree` / `decodeForest` 沿数值严格下降实现结构码的
计算逆向解析；往返与反向规范性同时成立。`SyntaxDecode.formula_encode_of_decode`
补齐当前十一种公式构造子的反向规范性。局部头部读取因此能恢复精确 AST 结论，
并验证实际自由上下文长度。

`ProofTreeCode.localCheck` 读取当前节点和子节点头部，使用现有 27 类逻辑公理解码器、
实际公理包解码器、`forallFreeTop`、`weakenFree`、`substituteFree` 等当前核操作。
`localCheck_encode` 证明每个类型正确证书都通过局部检查；`localCheck_sound` 证明
局部检查成功且各子证明可回放时，当前节点也能由普通 Hilbert 核回放。
`nodeChecked_encode`、`checked_sound`、`checked_complete` 将这些单步性质连接为
整棵树的可靠性与完备性，根节点还强制自由上下文为空、结论码精确匹配。

`ReducedProofTree.codec` 消费 `ReducedAxiomPacket`。已经具体证明：

```lean
ReducedProofTree.derives_iff (formula : SetSentence) :
  Derives intrinsic_zfc_theory [] formula ↔
    ∃ code, ReducedProofTree.checked code formula = true
```

递归对象图使用 `ObjectHorn.check` / `ObjectCheckedTrace.check` 的有限参考检查器。
规则赋值在当前行所界定的有限范围内枚举，递归沿显式秩下降；这是可计算的表示规格，
并非适合实际大证明码的高效执行器。`Descending` 必须显式证明，因为仅要求对象轨迹
对规则封闭不能自动排除循环自支持。

`ObjectProofTree` 使用六种节点形状和两类行，共 12 条规则。节点行调用局部测试并
递归检查子节点，根行连接闭上下文及声明结论。正向构造有限闭合轨迹，负向按秩排除
任意候选对象轨迹；不假定对象轨迹标准或已由宿主解析。`ProofTreeCode.ofLocalTest`
进一步完成数值结论到当前紧凑 quotation 的对象等式传输，并装配标准
`Delta1ProofPresentation` 接口。

完整公式识别图 `ObjectFormulaSyntax` 则已具体完成：固定 145 条规则覆盖 76 个函数
符号、55 个关系符号及十一种公式构造子，分别记录 bound / free 长度。
`checked_decode` 对任意自然数证明接受恰好对应实际 quotation 与 AST 解码成功，
`positive` / `negative` 给出同一固定 Delta0 公式的普通正负推导。输入大小、量词深度
和变量编号均无固定上限。

## 具体局部对象表示与完整实例

这里的 LocalTest 是固定对象公式所表示的单步合法性判定，不是样本或回归测试。
`ObjectSyntaxTransform` 以同一 28 条 Horn 规则表示四种变换：自由加强、首自由变量抽象、
首束缚变量实例化、有限项表给出的同时自由代入。`SyntaxTransformKernel` 证明通用
保类型代入交换律，`SyntaxTransformInstances` 将四种模式逐一接到实际内核操作。
候选输出可以是任意自然数；成功、错误输出和解码失败均有相应正负对象推导。

`ObjectLogicalAxiom` 列出全部 27 类有限模式，每个查询消费完整公式/项识别图或变换图。
`checked_number_iff` 恢复实际 Hilbert 公理证书及精确结论码，`checked_decode_iff`
在任意自然数证书码上与现有逻辑公理解码器对应。`ReducedAxiomNumber` 则将已完成的
ZFC 模式关系与有限公理表统一成任意数值结论的二元正负表示。

`ObjectLocalDecision` 为有限模式提供有界存在连接。`ObjectProofNode` 用六个模式
检查规范节点，子证明只通过 `ObjectProjection` 读取头部；中间见证的界来自当前
结论或子头部。已经证明：

- `ObjectProofNode.checked_sound`：接受蕴含原 `ProofTreeCode.localCheck` 接受。
- `ObjectProofNode.checked_encode`：任意实际 Hilbert 证明节点的编码均被接受。
- `ObjectProofRow.localTest_checked`：一元行封装在全部自然数上精确实现 `rowCheck`。

节点对象算法使用规范外壳，不声明它与原局部算法在非规范输入上的逐值相等。
整树装配 `ObjectProofNode.ofNodeTest` 消费上述可靠性及编码接受完备性，递归验证全部
子证明，并保持原理论的普通可证性。其参考检查器采用有限枚举，目标是形式化表示，
不承担实际大证明码的高效执行。

```lean
ReducedProofPresentation.nodeTest :
  ObjectCheckedTrace.LocalTest intrinsic_zfc_theory

ReducedProofPresentation.reduced :
  Delta1ProofPresentation intrinsic_zfc_theory ReducedAxioms.theory

ReducedProofPresentation.presentation :
  Delta1ProofPresentation intrinsic_zfc_theory intrinsic_zfc_theory
```

这三个定义都已具体填入所需对象条件、分类证明及正负普通推导，没有遗留的
LocalTest 参数。最终接口同时具备全树检查可靠性、可证性接受完备性及当前 quotation
的正负表示。`ProofTreeCode.ofLocalTest` 仍是供逐值相等检查器使用的通用入口。

本结果表示原支撑理论的证明关系；下节已将其装配为该理论上的具体 Rosser 不完备实例。
将支撑语言与支撑公理消去到裸 ZFC 仍不包含在当前结果中。

## 当前 quotation 的具体固定点与 Rosser 终局

`ObjectNumeralSyntax` 用两条固定递归规则表示实际 numeral 项的内核编码，给出任意
标准输入、任意候选输出的正负普通推导。`ObjectDiagonal.substitution` 复用完整
同时自由代入图，以单槽项列表表示一元公式的实际自由代入。

原始关系的逐数码正负表示不足以排除非标准对象输出。`ObjectMinimumRelation` 在
关系中要求输出属于既有码域，并且不存在更小的合法输出。`ObjectLeastWitness.unique`
围绕实际正确输出使用 `Core.cut_elim`：较小错误输出由有限负实例排除；较大候选
与正确输出已经合法矛盾。由此得到任意对象见证的唯一性，没有加入对象反射或新的公理。

`ObjectDiagonal.relation` 在对象公式内依次连接最小 numeral 项码和最小代入结果。
对于任意一元公式 `body`，`positive` 证明自代入结果存在，`unique` 证明任意满足关系
的对象输出等于实际句子 `instantiate body (code body)` 的自然数码。

给定一元模板 `P`，构造正文 `θ(x) := ∃ y (relation(x, y) ∧ P(y))`，再令
`fixedPoint := θ(num(code θ))`。存在性和唯一性分别给出固定点等价的两个方向；
`IntrinsicQuotation.quote_evaluate` 将实际自然数码传输回当前结构 quotation。

```lean
ObjectDiagonal.fixedPoint_spec (S : ObjectDiagonal.Support T) (P : FormulaTemplate.Unary) :
  Derives T [] (ObjectDiagonal.fixedPoint S.core.code_domain P ↔ₘ
    P (IntrinsicQuotation.quote (ObjectDiagonal.fixedPoint S.core.code_domain P)))
```

具体 `ReducedRosser.diagonalSupport` 的全部字段都来自原支撑理论中已证明的能力。
`ReducedRosser.presentation` 使用完整新证明图和后继链码域装配有限比较。
`ReducedRosser.sentence` 把上述固定点应用于 Rosser 比较的否定，`fixed_point` 给出
理论内的等价证明，最终接口为：

```lean
ReducedRosser.independent
  (hConsistent : Derives.Consistent intrinsic_zfc_theory ([] : Context signature [])) :
  (¬ Derives intrinsic_zfc_theory [] ReducedRosser.sentence) ∧
    (¬ Derives intrinsic_zfc_theory [] (¬ₘ ReducedRosser.sentence))
```

这里的一致性是唯一待假定的数学前提，不是本仓已经证明的一致性结论。固定点、
局部测试、整树表示及有限比较均已具体实现。目标理论仍是 `intrinsic_zfc_theory`；
尚未把支撑语言及支撑公理消去到裸 ZFC。

## 裸 ZFC 消去层：关系式翻译及首批具体定义

`Automation.RelationalTranslation.Interpretation` 为源排序指定目标排序，为每个
函数及关系指定固定目标公式。函数正文的自由槽顺序是“输出、各输入”。`term` 和
`arguments` 互递归生成项图，`existsBlock` 关闭任意元数的新参数见证；`formula`
保留所有逻辑构造子，等式由两个项图共享一个输出见证，`sentence` 直接生成目标闭句。

`RelationalEnvironment` 已证明模板代入、异质值列、bound 块提升及存在闭合的语义。
`RelationalSemantics.term_correct` 与 `arguments_correct` 证明图成立恰好表示实际值
相等；`formula_correct` 覆盖所有十一种公式构造子及任意量词嵌套，`sentence_correct`
给出目标模型与源扩张模型中的闭句真值等价。

`RelationalExpansion.Functional` 要求固定函数图对每个对象参数列存在唯一输出。
`expansion` 在元层选择该输出以构造模型解释；`expansion_realizes` 证明实际构造
实现全部函数和关系定义，没有增加对象语言选择算子。`models_iff` 连接翻译理论与
源扩张模型，`derives_sound` 将普通源 Hilbert 推导传为目标模型中的真值。
这一接口是语义传输，尚不是目标理论内的普通 `Derives` 变换或句法保守性定理。

具体目标 `ProofT.ZFC.PureModel.theory` 是原 `SetTheory.ZFC` 经 `Project.fo_theory`
得到的纯签名 `ℒ` 理论；没有并入 `intrinsic_proof_theory`。`PureModel` 直接解释
外延、空集、配对、并集和幂集公理，并由配对、并集构造单集与后继。

`PureFunctionDefinitions.Primitive` 由原支撑签名的实际函数符号索引，当前包含空集、
无序对、单集、并集、幂集、后继。`graph` 给出其实际纯隶属公式；统一的
`comprehension_correct` 证明成员条件的准确性，`comprehension_unique` 用裸 ZFC
外延性证明唯一性，`functional` 对这六种函数的任意参数证明存在唯一输出。
这些定义可直接填入完整关系解释的函数字段，不使用额外支撑理论模型作前提。

**尚未完成的边界：**全部原支撑函数及关系的纯定义还未填齐，全部支撑公理翻译在
裸 ZFC 中的证明及句法保守性也未完成。当前已完成的不完备定理仍是
`ReducedRosser.independent` 所陈述的支撑理论实例。

## 版本 1 数据包

宿主传输格式由 `ProofT.NatPacket` 定义，与旧 `ProofCode` 配数格式分别命名。
目前没有声明两者相同，也没有把旧对象图直接用于新格式。

1. 原始有限树为 `Tree.node tag children`，标签与子树数量均为自然数。
2. token 顺序为版本号 `1`，随后先序遍历每个节点的「标签、子树数、各子树」。
3. 每个 token 使用规范 unsigned LEB128：每字节低七位是数值位；最高位表示后续字节。
4. 若字节列为 `b₀,…,bₖ₋₁`，输入自然数为 `Σᵢ bᵢ·256ⁱ + 256ᵏ`。
   最高位字节 `1` 是终止标记。解码必须恰好消费全部数据。

`NatPacket.decode_encode` 已证明任意有限数据树的传输往返；
`NatEncode.tree_roundtrip` 证明全部六条规则的证书往返，二者组合为自然数往返定理。截断、尾随 token、未知版本和非规范 varint 均拒绝。
字节解析按自然数值递减，树 token 解析燃料取自输入长度；语法和证明解码沿有限子树
直接递归。这些递归都没有固定的证明长度或公式级别上限。

下表以 `N(t; x₁,…,xₙ)` 表示节点，以 `L(n) = N(n;)` 表示数值叶子。
这只是本页的数据记法，不是新增对象语言符号。

## 项、公式与替换

上下文为 `L(n)`，表示 `n` 个唯一排序 `SetSort.set`。
函数与关系编号固定为 `SyntaxDecode.functionSymbols`、`relationSymbols` 数组中的零基位置；
当前分别有 76 与 55 个符号。参数数目严格由 `signature` 检查。

| 项 | 树 |
| --- | --- |
| 束缚变量 | `N(0; L(index))` |
| 自由变量 | `N(1; L(index))` |
| 函数应用 | `N(2; L(symbol), argument₁, …)` |

变量索引从上下文头开始，必须小于对应上下文长度。替换参数列为
`N(0; term₁, …)`，长度必须恰好等于源自由上下文长度；各项在目标上下文中解码。

| 公式标签 | 参数 |
| --- | --- |
| 0、1 | 无参数，分别为假、真 |
| 2 | 关系编号叶子及符合签名的项参数列 |
| 3 | 两个项：相等 |
| 4 | 一个公式：否定 |
| 5、6、7、8 | 两个公式：合取、析取、蕴涵、双条件 |
| 9、10 | 一个公式：全称、存在；解析正文时增加一个束缚变量 |

## 公理证书

顶层 `N(0; zfc)` 是 ZFC 公理像，`N(1; support)` 是原支撑公理理论。

ZFC 固定标签 `0,…,7` 依次为外延、空集、配对、并集、幂集、无穷、正则、选择，
均不带参数。`N(8; L(n), body)` 是分离 schema，`N(9; L(n), body)` 是收集 schema。
它们分别在束缚深度 `n+1`、`n+2` 解码，并检查 `FreeClosed`。

Project schema 项仅允许 `N(0; L(index))` 形式的有效束缚变量。
Project 公式标签 `0、1、4,…,10` 与上表一致，`2` 接收两个项表示成员关系，
`3` 接收两个项表示外延相等，`11` 接收两个项表示子集。

支撑公理严格沿 `IntrinsicAxiomCertificate` 的呈现结构解析：

| 呈现 | 证书树 |
| --- | --- |
| `singleton` | `L(0)` |
| `union` 左、右分支 | `N(0; child)`、`N(1; child)` |
| `insert` | 与 `union (singleton …) …` 相同 |
| `indexed` | `N(0; index, child)`；先解析索引，再解析该索引对应的证书 |

参数化分离族的索引依次是自由上下文和该族全部项参数；项均在该上下文中解析。
132 个支撑呈现层都有对应的可计算解码函数，包括嵌套 `insert` 的各固定公理。

## 逻辑公理与推导规则

逻辑公理节点的标签按 `HilbertBaseAxiom` 构造子顺序固定。

| 标签 | 构造子 | 参数 |
| --- | --- | --- |
| 0 | implication_distribution | 三个公式 |
| 1 | self_implication | 一个公式 |
| 2 | weakening | 两个公式 |
| 3 | contradiction | 两个公式 |
| 4 | classical | 一个公式 |
| 5 | explosion | 两个公式 |
| 6 | case_analysis | 两个公式 |
| 7 | truth_intro | 无 |
| 8 | falsum_elimination | 一个公式 |
| 9、10 | negation_intro、negation_elimination | 一个公式 |
| 11 | conjunction_intro | 两个公式 |
| 12、13 | conjunction_elim_left、conjunction_elim_right | 两个公式 |
| 14、15 | disjunction_intro_left、disjunction_intro_right | 两个公式 |
| 16 | disjunction_elimination | 三个公式 |
| 17 | biconditional_intro | 两个公式 |
| 18、19 | biconditional_elim_left、biconditional_elim_right | 两个公式 |
| 20 | forall_specialization | 一个新增束缚变量下的正文、实例项 |
| 21 | forall_distribution | 两个新增自由变量下的公式 |
| 22 | vacuous_forall | 当前自由上下文的公式 |
| 23 | exists_introduction | 一个新增束缚变量下的正文、实例项 |
| 24 | exists_elimination | 新增自由变量下的正文、当前自由上下文的结论 |
| 25 | equality_substitution | 两个项、一个新增束缚变量下的正文 |
| 26 | equality_reflexivity | 一个项 |

证明树在给定自由上下文中递归解析；公开自然数入口从空上下文开始。

| 规则标签 | 参数及检查 |
| --- | --- |
| 0 | 逻辑公理树 |
| 1 | 顶层理论公理证书树 |
| 2 | 前提证明、蕴涵证明；前提结论必须等于蕴涵左端 |
| 3 | 新增一个自由变量下的证明；输出全称一般化 |
| 4 | 当前上下文的目标公式、增大上下文中的证明；后者结论必须等于目标的 `weakenFree` |
| 5 | 源上下文、替换参数列、源上下文的证明；输出统一替换后的结论 |

所有多余或缺失参数、未知标签、非法作用域以及规则连接错误均返回 `none`。
公式连接检查使用已有结构码的可计算相等判定及其单射定理。

## 验证

编码往返、检查器可靠性与完备性、实际解码器一致性以及对象正负表示，均由正文中的
通用定理提供。正式源码不再维护枚举样本或重复应用定理的专用回归模块；验证依赖
Lean 内核对正式证明的检查和全库构建。

```bash
lake --wfail build
bash scripts/check-all.sh
```

全库脚本构建全部正式源模块及 `prove_auto_sweep` 工具，warning 会使构建失败。
新入口已从 `YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory` 导出。

依赖审计：本轮没有新增 `sorry`、`admit`、自定义 `axiom` 或 `native_decide`。
入口仍继承原 Project 八条固定公理闭性检查中的八个既有 `native_decide` 依赖，
以及 `propext`、`Quot.sound`。往返与完备性证明还使用 Lean 标准的
`Classical.choice`；编码函数本身没有通过经典选择抽取证书。
此处不声称消除了原有 `native_decide` 计算依赖。

新 quotation 的 `unquote_quote`、`quote_injective`、`quote_ne` 经 `#print axioms`
审计仅依赖 `propext`、`Quot.sound`。具体支撑理论上的模式结论比较及旧码冲突审计
仍继承原 Project 固定公理闭性依赖，未新增 `native_decide` 或自定义公理。
`CodePattern` 的通用负向证明及 `bounded_exists_numeral_neg` 经审计只依赖
`propext`、`Quot.sound`；正向证明还继承既有 numeral 成员证明的 `Classical.choice`。
具体外壳和项作用域的正负证明继承原支撑理论的七个固定公理闭性依赖，
未增添 `native_decide`、解释符号或对象公理。
正文识别的双向判准、有限表重命名的成功/失败规格、实际模式位置及新 quotation
交换律经 `#print axioms` 审计，仅依赖 `propext`、`Quot.sound`。
新增 `ObjectHorn.positive`、`negative` 和重命名接受/拒绝证书经审计只依赖
`propext`、`Classical.choice`、`Quot.sound`；正文拒绝证书只依赖 `propext`、`Quot.sound`。
具体 `positive_at_tree`、`negative_at_tree` 与六个模式位置出口继承上述七个原有
固定公理闭性依赖，未新增 `native_decide`、`sorry` 或自定义公理。
模板通用负向编译、`template_delta0`、`run_isSome` 和实际替换装配的依赖审计
只出现 `propext`、`Quot.sound`。具体支撑理论的模板出口继承相同七个原有
固定公理闭性依赖；数值求值及负向算术还使用 `Classical.choice`。
本轮未新增 `sorry`、`admit`、自定义公理或 `native_decide`。
闭合拒绝证书依赖 `propext`、`Quot.sound`；传输规范性、包证书及通用包正负
编译依赖 `propext`、`Classical.choice`、`Quot.sound`。两套具体支撑理论出口
仍继承同样七个既有固定公理闭性依赖，未新增 `sorry`、自定义公理或 `native_decide`。
表生成与连接图的依赖审计只增加了普通 Lean 证明；`positive`、`negative` 和三类
实际闭句出口仍仅继承上述七个既有固定公理闭性依赖及标准 Lean 逻辑依赖。
本轮没有新增 `sorry`、`admit`、自定义公理或 `native_decide`。
模式包的新审计中，`packet_bound`、`run_le`、`project_formula_code` 和
`run_eq_actual` 只依赖 `propext`、`Quot.sound`；任意自然数包候选的拒绝证书还使用
`Classical.choice`。`SchemaPacket.actual_positive_number`、`actual_negative` 与独立
替换 quotation 出口继承原支撑理论同样七个固定公理闭性依赖，没有扩大可信计算边界。
基础公理层的 `AxiomCanonical`、`BaseAxiomPacket.checked_run`、`checked_sound`、
`checked_complete` 均有独立依赖审计；具体表示 `BaseAxiomPacket.presentation` 仍继承
标准 Lean 逻辑依赖，以及八个既有固定公理的闭性验证依赖。与仅有模式分支的七个依赖
相比，合并层因覆盖选择公理而额外引用已有的 `Axioms.choice._native.native_decide.ax_1`。
此次没有新增 `sorry`、自定义公理声明或 `native_decide` 调用。
参数证书层的项规范性、外壳规范性和 `SupportParameters.actual_eq_decode` 经审计只依赖
`propext`、`Quot.sound`；通用接受、拒绝及推导编译还使用 `Classical.choice`。
具体 `ZFC.SupportParameter.positive`、`negative`、`encoded_positive` 仍仅继承上述七个
既有固定公理闭性依赖，未新增 `sorry`、`admit`、自定义公理或 `native_decide` 调用。
参数装配层沿用普通 Lean 定理与原有公理呈现的可靠性证明，未新增 `sorry`、`admit`、
自定义公理或 `native_decide` 调用，也未新增枚举回归模块。
有限公理基及其对象表示使用普通全称消去、项代入、全称引入、理论 cut 与既有有限表
正负证明，没有新增 `sorry`、`admit`、自定义公理、`native_decide` 或回归样例。
本次稳定基点通过默认构建、全部 629 个 Lean 模块及 `prove_auto_sweep`，warning 为零。
