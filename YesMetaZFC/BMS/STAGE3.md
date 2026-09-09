# BM4 良序性形式化：Stage 3

## 权威陈述

本阶段对应 Rachel Hunter, *Well-Orderedness of the Bashicu Matrix System*,
[arXiv:2307.04606v3](https://arxiv.org/abs/2307.04606), Lemma 2.6。将普通严格序记为 `<`，第 `k` 层稳定关系记为
`<ₖ`。若 `ω < α <ₙ β`，并且有限集 `X` 位于 `α` 下方、有限集 `Y` 位于
`[α, β)` 中，则可把 `Y` 反射为 `α` 下方的同大小有限族，同时保留：

1. `X` 到 `Y` 的全部真实 `<` 与 `<ₖ` 事实；
2. `Y` 内部的全部真实 `<` 与 `<ₖ` 事实；
3. 对 `m<n`，`Y` 到 `β` 的 `<ₘ` 事实反射为图像到 `α` 的事实。

论文第 7 页把第三类原子写成 `φ₂(η,k)`，其语义是
`L_η ≺_{Σ_(k+1)} L`，并引用 E. Kranakis,
*Reflection and partition properties of admissible ordinals*, Theorem 1.8，
说明这是 `Π_(k+1)` 可定义的。这里的右端是当前环境中的构造宇宙，而不是一个
可作为参数传入的小层集合；这一区分是 Stage 3 最后接口的语义验收条件。

## 2026-09 上游重构后的依赖边界

- YesMetaZFC `b36e243` 已把一阶语法重构为
  `Formula σ bound free`、`Term σ bound free sort` 与内在类型化变量；旧的
  `FreeVarId`、无类型公式以及兼容层不再作为 BMS 桥接依据。
- `StageStructure`、`FormulaTranslation` 与 `ExternalLevyHierarchy` 已改写为
  新 bound/free 上下文；翻译把外部 `Fin n` 元组逆序放入 de Bruijn bound 栈，
  并保留逐公式 Tarski 语义。
- 具体的 `stageStableLt` 以 constructible 依赖库的 `FOFormula.Satisfies` 为
  规范语义；YesMetaZFC 的新内在语法只承担有限 Lévy 复杂度证书和反射编译。
- 上游 `FormalSystem.TarskiTruth` 当前给出对象理论的定义公理，不给出这些
  符号在 `L` 中的解释正确性；它不能被引用成环境真谓词定理。
- constructible 依赖库的 `CodedSatisfaction` 只处理集合大小的固定载体，文件
  自身也明确排除 ambient truth。它可用于 `stableBetween`，不能直接 discharge
  `stableToUniverse`。

## 已完成

- `StabilityFrame` 封装良基严格序与逐层稳定关系；
- `StableRepresentation` 精确编码有限数组的严格保序标签和 ancestry 保持条件；
- `FiniteReflectionInput` 以 `Fin` 索引族保留论文中有限 `X,Y` 的精确对应；
- `FiniteReflectionWitness` 编码 Lemma 2.6 的五类结论；
- 已证明任意保序反射见证的图像函数为单射；
- `IsSigmaFinite` / `IsPiFinite` 已将 YesMetaZFC 的 Lévy 语法层级从第一层推广到任意有限层；
- 已证明右结合有限合取、有限存在闭包保持 `Sigma_level`。
- 已定义单 sort、无函数的有限图签名及其 Tarski 结构；
- 已将六组关系约束编译为对象语言公式，并证明满足关系与
  `FiniteReflectionWitness` 双向对应；
- 已按论文量词范围修正稳定关系：`X→Y` 与 `Y→Y` 保持所有
  真实 `<ₖ`，只有“图像到下边界”限制 `m<n`；
- `FiniteLevelSupport` 精确记录论文“`σ` 以下每对序数仅有有限多个
  真稳定层”的前提，并已证明两个有限族的全部 `X×Y` / `Y×Y`
  关系共享一个有限 `stabilityCutoff`；
- 已区分“含原 `Y` 参数的审计图”与“只编译原图上真关系的可反射图”；
- 可反射图只含 `X`、候选图像和下边界参数，原 `Y`与上边界不进入小结构；
- 两种有限图都已证明为 `Delta0`，其有限存在闭包已证明为 `SigmaFinite 0`；
- `CompiledDiagramReflectionProperty` 到 `FiniteReflectionPrinciple` 的无缺口定理已完成。
- 已用逐变量 `∃x (closeFreeAt x …)` 取代无语义证明的统一闭包，并证明
  其满足关系精确等价于存在 `Fin upperCount → Label` 见证；
- 已证明自由变量批量赋值保留 `X` 参数并精确写入所有图像变量；
- 已修正反射公式的两个模型论错误：`Y′<α` / `Y<β`
  由同一一元 `belowTop` 公式在两层的不同解释给出，
  `f(δ)<ₘα` / `δ<ₘβ` 同理由 `stableToTop` 给出；
- 已证明大结构中的原 `Y` 满足已闭反射句，以及小结构句子见证到
  `FiniteReflectionWitness` 的完整提取管线；
- `IsSigmaFinite.closeFreeAt` / `IsPiFinite.closeFreeAt` 和级别单调性已完成；
- `IsSigmaFiniteElementaryAt` 已固定有限 Lévy 初等性的双向语义接口。
- `CompiledTargetBaseParameters` 已证明大结构只需携带 `X`
  参数；原 `Y` 由已闭句子的存在量词在内部引入；
- `CompiledElementarityWitness` 已固定小、大编译图结构之间的
  `Sigma_0` 初等嵌入数据，并证明大结构的原 `Y` 见证反射为
  小结构中的已闭句子见证；
- `finiteReflectionPrinciple_of_compiledElementarity` 已将有限初等性
  直接连接到 Lemma 2.6，`ReflectionWellOrderingData.ofCompiledElementarity`
  已进一步连接到 Stage 4 最终模型。
- 当前 `stabilitySignature` 只是编译有限关系图的中间语言；
  其原子关系在该中间语言中为 `Delta0`，不可直接冒充为
  集合论成员语言中的 `Delta0` 公式。具体层级实例必须另外证明
  `<_k` 与“到 `Ord`”谓词的集合论可定义性及正确复杂度。
- 已将稳定关系的层级向下单调性和 `σ` 以下无全层稳定对
  封装为 `LevelMonotone` / `NoFullyStablePair`，并无穷下降地推出
  `FiniteLevelSupport`；`ofMinimalStableBoundary` 已把这一纸面的
  `σ` 极小性论证接入最终模型组装器。
- 已对全部外部成员公式同步迭代反射闭包，并经反向语法翻译证明所得层在
  YesMetaZFC 原生公式语义下对所有有限 Lévy 层初等；
- 已把论文假设 `ω < α` 纳入具体 `stageStableLt` 定义；全反射起点会规范地
  提升到 `succ ω` 之上，并已证明稳定对两端的可构造层都包含内部阶段求值器
  所需的十三个规范参数。该结论只解决参数存在性，一般小层中的阶段历史
  存在性与公式正确性仍须单独证明；
- 已由序数良基性选出规范的最小全稳定边界；
- 已从该边界的全稳定后继连续三次反射单点，构造每个有限高度所需的
  `lower < upper < bound` seed，最终装配不再要求调用者提供边界或 seed。
- `externalExistentialClosure_l` 已证明任意有限个末尾坐标的存在闭包语义，
  `translateExternalBinaryAt` 已证明二元自由变量翻译保持满足关系；
- `internalLStagePairFormula_l` 已将十三个规范参数全部存在量化，证明所得
  二元公式在整个 `L` 中精确识别外部 `L_alpha`，并在全反射层中传递该语义。
  这不等同于已经证明一般有限初等层的局部正确性或所需的低 Lévy 复杂度。
- `TextbookLevyTrace` 已将原来的 Sigma/Pi 归纳码证书转换成逐行有限记录，
  并证明可计算检查器接受当且仅当记录合法，合法记录存在当且仅当原分类成立；
- `TextbookLevyIndexedTrace` 已将递归检查等价转换为有限图上的严格前驱索引条件，
  不再需要在对象语言中解释 Lean 的递归计算；
- `ExternalDelta0Translation` 已证明外部有界公式的翻译确实保持原生 `Delta0`，
  并给出原生 `Delta0` 中不属于旧外部 Sigma 零层的句法反例。
  因此旧外部码分类器与原生有限层级不能未经证明就视为同一个句法类；
- `TextbookLevyRecordZF` 已具体编码记录和有限索引图，证明编码单射、可构造性、
  成员语言记录格式公式的精确语义、唯一解码和最低有限 Sigma 复杂度；
- `TextbookLevyTraceGraph` 已构造严格先前引用的 `Delta0` 成员公式，并证明它
  在规范索引图上恰好表示检查器所用的列表前缀成员关系；
- `TextbookLevyRecordAbsolute` 已证明记录格式公式在任意包含标准 omega 的
  传递载体中正确，特别适用于所有 `omega < theta` 的 `L_theta`。
  这个局部正确性结论只针对有限语法记录，不针对跨序数的阶段求值历史；
- `TextbookLevyTraceBounds` 已证明每份规范有限证书属于 `L_omega`，从而任何
  `omega <= theta` 的层都含有已分类记录所需的真实有限证书；
- `TextbookLevyTraceTests` 使用内核 `decide` 检查三个接受例和四个拒绝例；
  `ProofAudit` 对关键构造和最终条件定理逐项输出内核公理依赖。
- `NativeDelta0Representation` 已反向构造真正的外部 `Delta0Formula`：每个
  原生成员语言 `IsDelta0` 证明在任意非空成员结构中都有逐赋值等价的有界
  外部公式；该构造覆盖有界存在、有界全称与 guarded existence；
- `NativeFiniteLevyRepresentation` 已把上述底层表示同步提升到全部有限
  `Sigma/Pi` 层，所得外部公式保留原层级并具有结构无关的统一语义；
- `BoundedExternalStageElementarity` 已证明完整有界外部有限层初等性与项目原生
  `StageSigmaElementaryAt` 双向等价。因而旧外部片段遗漏有界全称的问题已经
  在语法和模型两侧都得到修复，原生有限 Lévy 层级兼容性不再是剩余假设。
- `LocalStageFormula` 已接入上游 `CanonicalBareHistoryGlobal`、
  `BareStageCorrect` 与 `StandardCondensation`：对每个严格高于 `omega` 的
  后继极限 `theta` 及每个 `alpha < theta`，二元公式
  `localLStagePairFormula_l` 在 `L_theta` 中无条件且唯一地识别真实的
  `L_alpha`。其原生自由变量版本 `stageLocalLStageFormula_l` 也已给出逐环境
  语义定理；这一结果不再要求环境层对整个 `L` 全初等。
- `TextbookLevyEarlierRecordAbsolute` 已把有界前缀图查询与记录字段绝对性组合，
  证明八元“严格先前记录”公式在任意传递集合中绝对；五个局部规则接下来只需
  分别处理其有限自然数见证，不再重复图查询与记录解码。
- 五个局部规则、完整痕迹和五元分类器均已完成任意 `omega < theta` 后继极限
  层中的局部绝对性；分类器的任意见证还可规范化为真实有限痕迹。
- `StageRelativization` 已证明任意固定外部公式相对化到一个已命名的 `L_theta`
  后成为真正 `Delta0`，并且其在更高层中的语义精确等于原公式在 `L_theta`
  中的语义。
- `TextbookLevyClassifierBounded` 已把完整有限分类器的所有量词限制到内层
  `L_theta`，得到原生 `Delta0` 分类器，并证明它在任意更高可构造层中仍精确
  刻画同一分类证书；这消除了旧外部公式表面交替秩造成的错误复杂度上界。
- `RelativizedLocalStageFormula` 已在已给出右端阶段 `L_beta` 时，用真正
  `Delta0` 公式于任意 `L_top` 内精确识别所有 `L_alpha`（`alpha < beta < top`）。

## 剩余工作

1. 在不加入真谓词公理的前提下，构造固定有限 Lévy 层的环境满足公式，并证明
   它与外部 Tarski 语义双向等价；
2. 将编译图余下的稳定原子翻译为成员语言公式：两个集合大小 `L` 层之间的
   统一稳定关系和 `η <_m Ord`，分别证明所需的低复杂度及有限初等层中的
   精确局部语义。左端阶段在右端阶段已命名时已由相对化公式降为 `Delta0`；
   当前关键缺口正是论文 `φ₂(η,k)`：右端必须是当前 ambient `L_top`，不能用
   一个被命名的集合层代替；
3. 用上述公式实例化已经收缩后的 `ConstructibleStabilityFormulaData`，
   从最终装配中消去最后一个参数并进行全仓库验证。

Stage 3 在上述剩余工作完成以前不算完成。
