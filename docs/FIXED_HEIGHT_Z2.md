# 固定行数的 Z₂ 逐实例路线

## 本轮目标

对每个外部固定的标准自然数 N，争取构造 Z₂ 对当前行数不超过 N 的
生成 BM4 数组良序性的推导。不声称 Z₂ 内的统一全称结论；
也不把“等一致背景中可证”当作“Z₂ 中同一句子可证”。
这是一条重新启动的研究路线，尚未完成。

## 已完成的第一步：精确行数目标

FiniteHeight.carrier_l N 包含所有当前行数 ≤ N 的生成数组，不限制
其生成历史的种子高度。FiniteHeight.step_l 是原严格一步关系的限制。

- wf_iff_l：该限制良基，当且仅当每个 n ≤ N 的精确高度纤维良基。
  反向消费已有 acc_bounded_l 的有限高度归纳，不用全局 BMS 良基性。
- descent_iff_l：有界载体上存在无限下降，当且仅当某个 n ≤ N 的
  精确高度纤维存在无限下降。证明使用不增高链最终恒定的已证引理。

这是两个实际宿主层等价定理，不是任何正高度良基性的新证明，
也还不是对象 Z₂ 推导。原始目标是限制后的严格序的良序性；
本步锁定其一步良基性核心，严格序／无限下降和对象句子的精确桥仍须保持。

## 本轮发现的循环风险

现有 expansionPath_endpoints_comparable_of_accessible 要求共同起点
的 Acc Step。LocalDescent.wellOrder_of_wf_l 的全局可比性调用又先消费
整个 GeneratedStep 的良基性。因此不能引用它来无条件论证：
“任意低行数生成矩阵都在某个固定高度种子之下”，再用该结论证明良基性。

一行 seed 的可达性不是所有一行矩阵良基性：其一次展开已经失去一行。
已有 seed_one_l 主要由零高度情形证明，不能把它当一行子系统的完整基例。

## 接下来实际需要的证明

**更新：下面第 1 项已有直接表示解法，不再把种子覆盖列为必要前置。**
FiniteHeightRepresentation.chain_l 在最小第 H+1 层边界 σ 以下，
对有限链长度归纳。单点反射把 σ 放到 β 中的上方见证复制到 σ 以下，
新标签在全部旧标签之上，同时保留 H 层稳定关系并 H 稳定于 σ。
于是可取列数加一的链：前面各项标记列，最后一项作为共同上界。
祖先所在行严格低于当前高度，因此链的 H 层稳定性足以保留所有祖先边。
representation_l 和 acc_l 已证明所有高度 ≤ H 的合法数组有界表示及可达性，
wf_l 接回精确的 FiniteHeight 目标；没有使用生成性或全局 BMS 良基性。

上述四定理已通过完整构建与审计，仍使用原宿主序数、D 及最小有限稳定边界前提。
这里 H+1 是稳定关系的层号，不是二阶算术公式的复杂度。
后续工作集中于第 2、3 项；不可据此宣称已经构造 Z₂ 的内部边界。

1. 先解决低行数生成矩阵的固定种子控制，或直接构造只依赖当前行数的
   稳定表示。前一路线必须不用全局 Acc 来证明需要的可比性／覆盖；
   后一路线则需要检查实际生成性质是否足以给出表示。
2. 对每个外部固定复杂度完成部分真值、真实有限图反射和上端点稳定边；
   复用 BMSTools 的收集、递归、赋值、证书工具。只固定 N，并不会使
   列数、展开指标或证明所量化的内部有限编码自动成为外部有界。
3. 将固定行数目标接到已有二阶代码呈现，证明完整解释的目标保持，
   最终给出对象 Z₂ 推导。若借用可数集合论，须证明足够的解释／保守性，
   不能仅用等一致性传输良序句子。

旧 ZFC／可构造证明及 BMSTools 入口保持原样。此轮不自动提交或推送。

## 背景转译的文献依据与未实现边界

Simpson 作者公开的第二版导论 I.13（印刷页 57、60；概述 VII.6、IX.4）
明确陈述强选择体系的保守性，特别是 Σ¹(k+1)-AC₀ 对 Π¹k-CA₀
的 Π¹min(k+2,4) 保守性。按每份推导只用有限多个模式实例，
可在纸面上得到 Z₂ 加完整可数选择模式对 Z₂ 的 Π¹₄ 保守性。
来源：[作者公开导论](https://sgslogic.net/t20/sosoa/chapter1.pdf)。
固定递归关系的无无限下降句子是 Π¹₁ 型，因此该保守性是一个
有文献依据的候选传输工具，而非仅有等一致性的类比。

但本仓库尚未形式化该保守性，也尚未构造“Z₂ 加选择”到所需
无幂集收集背景的全部解释。当前 SecondOrderTMC.models_l 的目标
仍是无收集、无选择的 TMC；绝不能直接向 PowerlessFiniteChain
传入这个模型证明。下一步须在以下两条中落实实际证明：
在 TMC 中构造所需相对可构造内模型并保持目标，或形式化足够的
选择扩张解释与保守性。上述文献不直接证明 BMS 句子。

## 内部有限链的实现

PowerlessFiniteChain 使用原 Formula AST 表达实际集合关系上的有限链。
chain_formula_l 核对语义，zero_l、append_l 构造实际有限函数图，
exists_l 对模型内部 ω 归纳。因此链长度可以是模型中的非标准自然数，
不依赖宿主 Nat 归纳或无限选择序列。该模块已独立编译。
serial_l 进一步把延长条件归约为关系非空、传递且每点都有后继：
内部自然数的零／后继分解给出末项，传递性保留全部旧标签关系。
这避免为了初始稳定链而反射随内部列数增长的外部公式合取。
其前提仍为 PowerlessTheory 以及每条有限链可延长；这些前提不能
自动由现有 Z₂ 弱集合论解释获得，必须另行闭合。

## 内部全局最小稳定边界

PowerlessGlobalBoundary.exists_l 从任一实际稳定对取全局最小下端点。
分离的载体是已给出的上端点 β，但候选条件是“存在某个上端点”，
其中存在量词不受 β 限制。正则性和 β 的传递性保证所得最小性
对所有上端点成立。cutoff_l 进一步证明边界以下任一稳定对的
层号严格低于边界层号。两定理已独立编译，聚合审计通过。
此处仍没有证明任意所需层号上有稳定对，不能把它记为边界无条件存在。
原 PowerlessStableBoundary 和 PowerlessBoundaryOrder 保留 κ 以下可变
上端点的接口；新模块不替换它们。一次同名覆盖在完整构建中被检出，
已恢复原文件并独立命名，修复后的完整验证另行记录。

## 局部真值接受证书的集合闭包

PowerlessTruthClosure 已独立编译。step_formula_l、certificate_formula_l、
accepts_formula_l 把原 Formula 的实际语义逐项连接到值谓词，未更改原检查式。
union_l 构造任意实际证书集合族的并；adjoin_l 添入满足局部规则的父记录；
base_l 由原有界识别和有符号有界真值构造初始接受证书。
collect_l 对给定记录集合，以原 certificate_m（不含 H）作收集条件，
再分离掉收集上界中的非证书成员，合为一个覆盖所有输入记录的实际证书。

这些定理在完整 PowerlessTheory 模型中成立。不能直接把当前小层
满足的 PowerlessFiniteStageEvaluation 当作完整核心来调用它们。
PowerlessTruthClosureSupport 已对原证书收集闭句取得实际 Hilbert 推导，
并从推导抽出有限核心公理列表。models_l 对只满足该列表的任意结构
给出原闭句，而非要求完整核心。该模块已独立编译。
尚须证明所需层满足此列表、补齐全部规则的接受完备性，再接有限层反射。
此轮没有证明稳定对存在，也未完成 Z₂ 的 BMS 推导。

后续完备性必须限定实际分类及极性：PowerlessTruthStep.step_m 的无界
存在量词分支显式要求 p = e，没有负无界存在量词规则。不能把该单个
accepts_m 当作对任意公式、任意极性都完备的全真值定义。任意外部固定
层号仍需要逐层部分真值构造与分类对应；集合证书闭包只补齐其中的
构造步骤，不消除层号或极性义务。

## 外部固定层号的原公式族与局部接受构造

PowerlessTruthInduction 按内部公式码归纳，不假定模型的自然数标准。
PowerlessTruthOracle 的低层调用参数 B 是原 Formula，使用原替换机制，
自由参数只有 ω,e,T,t₁,t₂,t₃,n,p,c,f，没有全局真值 H 或当前层 U。
sound_l / accepts_source_l 已证明：在显式低层可靠性前提下，新检查器可靠。
该前提尚未对整个递推族消去。

PowerlessPartialTruth.formula_m 按外部 Nat 产生实际有限原公式。
lower_m 通过内部后继关系读取前一层的 Σ 正接受、Π 负接受及其否定。
lower_sound_l / lower_complete_l 明确需要低层双向正确性；
只有可靠性不足以处理取反分支。zero_complete_l 从零层分类及有符号
有界真值构造实际初始接受；lift_complete_l 将低层调用的结果接入实际
后继公式。这些不是整个公式族的双向真值定理。

PowerlessOracleClosure 已构造实际证书的并、添入、低层初始记录、
收集、二元合并，以及同层与非、正无界存在量词的接受闭包。
original_l 不改动原证书记录就可进入新检查器。family_l 的收集条件
是调用者给出的实际原公式，并在合并前筛选掉收集上界里的非证书成员。
PowerlessOracleBounded 已完成有界量词正、负分支；负分支按实际界集合
收集更新证书，不假定界有限，也保留槽位非法及界槽无取值的原规则情形。

PowerlessOracleSupport 进一步对每个固定低层公式 B 证明了实际收集与
添入闭句，并从真实 Hilbert 推导抽出有限核心公理列表。
collection_model_l / extension_model_l 只要求小结构满足该列表，
返回原闭句在任意自由参数环境中的满足性，不要求完整核心。
单独这些接口不自动证明所需层满足该列表，也不提供整族双向真值定理。

PowerlessTruthIntroduction 现将有界识别、有符号有界真值到原接受
证书的蕴含闭合，抽取其实际有限支持。复用原十槽环境（零层忽略
层号槽），避免九／十槽环境的大规模展开比较。PowerlessPartialTruthZero
在真实层结构中以这一支持证明 formula_m 0 与完整层求值的有符号
真值双向对应，覆盖全部内部有界代码及层内有限赋值；未要求小层
满足完整 Core。零层 Lévy 分类可由 LevyZero.class_l 接到此结论。

PowerlessPartialTruthOne.lower_l 利用内部后继单射性，将第一层调用
的内部前驱还原为零；分类绝对性及零层双向对应处理包括取反的分支。
source_l 消去第一后继原接受公式的低层可靠性前提。不要求代码外部
标准，但仅证明第一层可靠性，第一层分类完备性尚未完成。

PowerlessTruthStage.exists_l 对任意外部有限低层公式列表，将求值、
零层引入及各 OracleSupport 的真实有限支持合并。在任意指定序数及
ω 之上构造同一个真极限层，返回实际编码参数、环境中的完整求值图、
零层双向对应、第一层可靠性，以及列表中每个原收集／扩充闭句的真值。
因此这些结果已有真正的层存在性消费者，不再预设小层满足支持。
完整求值图只服务于正确性陈述，不在部分真值源公式自由参数中。

PowerlessOracleRules 进一步以原 AST 表达完整局部接受构造：低层调用、
原证书、与非、正无界存在、有界正负量词。子公式各自有接受证书即可，
不要求预先提供共同证书；保留有界负分支的全称集合条件及非法槽位。
step_l 从环境 Core 中已证的实际构造给出父接受。
PowerlessOracleIntroduction 将全部规则闭合并抽取真实有限支持，
其 satisfies_l 只需该有限支持模型。TruthStage 的列表支持现同时包含
OracleSupport 与 OracleIntroduction，并返回每个原闭句在同一层为真。
因此下一步不再需要在小层中错误调用要求完整 Core 的构造接口。

PowerlessRelativeParameters 使用原 Substitution，将相对化后的原公式
接到任意环境；只有原参数属于域，域参数本身可以在域外。
PowerlessPartialTruthProperty 把实际接受完备性写成原语言正文，比较
环境中的 D/H 与小层中的 B。body_l/property_formula_l 核验其语义，
induction_l 以实际正文沿内部 ω 的代码序归纳；zero_l 用已有零层正确性
证明其零层实例。第一层全部构造子的推进现已在 PartialTruthProgress
和 PartialTruthFirst 中完成；这不是对任意有限层的归纳已经完成。

下一步务必区分两个公式角色：Property 的 B 是待验证的完整部分真值
公式（例如 formula_m 1），OracleIntroduction 的 B 是该接受公式所调用
的低层矩阵（例如原十槽 lower_m (formula_m 0)），不是 formula_m 0 本身。
证明第一层推进可参照 LevySound.sound_l 的五类分类记录分支。
PowerlessPartialTruthIntroduction.oracle_m 明确封装实际低层矩阵，
original_l 消费对应有限引入支持，将原零层证书送入后继公式。
bounded_l 覆盖全部内部有界代码、层内有限赋值及任意被忽略的层号参数；
该参数的零层双向正确性已在 PowerlessPartialTruthZero.source_l 中推广。
promotion_l 对目标层号不超过 1 的严格低层分类，证明内部 m = 0，再
消费零层双向正确性；不使用同一码的归纳假设，也不假设完整第一层结论。
PowerlessPartialTruthIntroduction.nand_l 已从两个子式各自的接受证书
构造父式接受；PowerlessPartialTruthProgress.boolean_l 已接入原内部
归纳性质：读取实际分类记录、证明两个子码严格更小、消费它们的归纳
假设，并按完整层求值方程核验极性。目标层号任意，不限于第一层。
PartialTruthProgress.bounded_l 已完成有界两种极性的实际推进；
quantifier_l 已完成第一层内的正无界存在，同极性沿严格子码归纳，
反极性从严格降层调用零层结果。

PowerlessPartialTruthFirst.complete_l 已消费五类实际分类规则，沿原
内部代码归纳装配接受完备性；source_l 与旧第一层可靠性合成原
formula_m 1 的双向正确性。范围是匹配分类极性的所有内部第一层
代码及层内有限赋值，不是外部标准代码枚举，也不是任意极性无条件
完备。PowerlessTruthFirstStage.exists_l 已把此结论接到实际层构造，
在任意给定序数及 ω 之上得到有该性质的真极限层，无预设小层存在性。

此前与非消费者的公式展开瓶颈已解决：EvaluationParameters 保留完整
求值见证的原递归公式真值，TruthParameters/OracleParameters 逐项
证明原检查式的参数语义，全部不要求模型满足 Core。它们不是更换求值
定义，亦不提供任何证书存在性。lift_formula_l 和 nand_formula_l
隔离大公式；先使用 Term.eval_weakenBound，再展开环境读取参数。
将两步合成一个整式 simp 会过早展开 Env.pushBound，导致移位定理
不匹配或巨量定义展开。无需提高步数上限。成功日志
bms-oracle-parameters-module、bms-partial-nand-parameters-module、
bms-partial-progress-module；旧 bms-partial-nand-module 仅记录失败探索。

量词推进的现有接线：PowerlessStageFiniteGraphs.finite_l 将任意内部
有限映射 g : k → U 放回真极限当前层（需 ω ⊆ δ）；
PowerlessValueAbsolute.update_l 比较小层与环境中的同一更新关系；
StageAmbientAssignments.slot_l 保留合法槽的准确条件；
PowerlessBoundedCode.equation_l 与 EvaluationEquations.exists_l 给实际
构造子的精确求值方程。OracleRules 的 witness/量词分支现已有与
nand_formula_l 同样的无核心参数语义，Introduction.exists_l/positive_l/
negative_l 消费它们产生原接受证书。负有界推进实际保留非法槽、界槽
无取值及全体界内元素，没有替换成有限枚举。


上述集合构造的证明仍使用完整 PowerlessTheory。一般后继步骤现由
PowerlessPartialTruthSuccessor / Step 完成：前驱唯一性和实际层分类
绝对性给低调用可靠性；分类单调性给任意严格降层；反极性存在分支
消费该降层证明。同极性沿严格子码归纳，五类分类规则全部装配后，
Step.source_l 给后继层匹配极性的双向正确性。它仍消费前驱层同性质
作为外部递推假设；没有把前提加强到任意极性完备，也未假定小层完整 Core。
PowerlessNumeral 已给真实外部有限数码的存在性、内部自然数性质和唯一性；
PowerlessPartialTruthFinite.source_l 已由零层与 Step.source_l 按外部 Nat
完成整个有限递推族。PowerlessTruthFiniteStage.exists_l 用实际低层矩阵
的有限列表反射支持，构造任意指定序数之上的同一个真极限层，使所有
j≤k 的原 formula_m j 同时具有匹配极性双向正确性。没有预设该层存在，
完整求值图仍只在环境中。该任意外部有限族和其实际层存在性已完成；
不能将这项部分真值结论等同于固定行数 BM4 良序或 Z₂ 终局。
随后仍须证明有限
稳定对存在、BM4 内部算法与任意下降实数的对应，以及实际 Z₂ 推导传输。
不能以原语法公式族、有限支持或局部规则已完成替代这些目标。


## 固定二元原公式的实际见证闭包

PowerlessOrdinalCollection 已证明部分定义关系的收集、任意实际序数集合的并
及严格上界；不预设共同上界 κ。PowerlessOrdinalMinimum 用实际分离与
基础公理选择满足固定原公式的最小序数，不调用对象理论的选择公理。

PowerlessSourceWitnessBound / Step / Sequence 将这些构造接到实际层次：
为固定二元原公式选择更高见证层，按模型内部 ω 递归，再取值域之并。
limit_l 得到真极限层，其中每个已在层内的输入，只要在环境模型中有
该公式的见证，就有层内见证。未把内部自然数当作标准 Nat。

这里明确要求完整 PowerlessTheory（含 Collection）。推进／序列存在性
现已将原全域覆盖弱化为：指定公式的见证属于某个实际层；没有更改结论。
PowerlessSourceWitnessDomain 用原公式表达该域，把见证限制到层次对象，
据此消去限制公式的覆盖前提。exists_l 仅从完整核心、ω、零与起始序数
构造更高真极限层：层内输入在层次类中若有原公式见证，就有层内见证。
没有全域覆盖、稳定对、对象 Choice 或全局真值集前提。

这不是任意 Z₂ 模型中的结论，也不是全公式初等性。PowerlessSourceClass
现已对任意固定原公式实现量词的类相对化及逐构造子语义对应，使用原
Formula 与 Substitution，没有另造源语法。domain_m 将带自由参数的
一元域公式代入量词变量；form_m 为每个量词增加域限制，保持原子式、
联结词与自由参数。formula_l 比较该翻译在环境模型中的真值和实际类
子类型结构中的原公式真值。只要求类非空及域公式解释正确，不要求
类是集合、满足 PowerlessTheory 或已具有初等性。全称与存在量词均
已证明对应，且没有使用内部自然数的外部标准性。

PowerlessHierarchyClass 已把实际层次域接入该通用接口：nonempty_l 由
实际相邻层的成员关系证明类非空，domain_formula_l 解释带参数的原域
公式，lift_l / env_l 提升类内环境并保持其实际值，formula_l 得到实际
层次类的逐公式相对化语义。它不再要求任意域解释条件；仍明确要求
环境里的所有变量属于类，这不是初等性或类满足核心的假设。

下一步仍须封装任意外部有限元数的见证请求，
完成子公式反射与实际部分真值的双向正确性。随后仍有有限稳定对存在、
BM4 实际算术表示和 Z₂ 推导传输。不能借用先要求稳定对的
PowerlessStageFiniteTheory.models_l 循环证明存在。

有限参数编码可复用 PowerlessStageGraphClosure.ordered_l（真极限层中的
实际有序对闭包）及 PowerlessBasic.ordered_eq_l（有序对坐标唯一性）。
PowerlessSourcePack 已以原替换把两个自由输入合并为一个有序对请求，
保持输出见证与其余自由参数。pair_l 用坐标唯一性给出原公式真值的
精确对应；closure_l 实际构造参数码再传回原请求。exists_l 结合已有
层次内见证闭包与极限层有序对闭包，构造对两个输入关闭见证的更高
真极限层；没有参数码存在前提，也不要求该层满足完整核心。

PowerlessSourceTuple 已完成任意外部有限元数的编码：复用
Values ℳ.Carrier (List.replicate n .set)，递归合并前两个输入；零输入
以实际层内空集作缺省码。code_exists_l 构造层内请求码，formula_l
逐次使用有序对坐标唯一性证明精确真值对应，exists_l 得到指定有限
元数公式的实际见证闭包层。这是外部语法元数，不是模型内部 ω 的
外部标准性假设，也不代表已经证明 n 行 BMS 良基。

PowerlessSourceFamily 进一步将有限多条请求合并到同一实际真极限层，
每条请求可以有不同元数，但保留同一尾部自由参数上下文。sum_m 用
两个互异标签区分请求，left_l / right_l 排除返回另一分支见证的可能；
不能用无标签的公式析取代替。family_closed_l 传回列表中的每条请求，
exists_l 消费实际有限列表 Σ n, Formula，并同时返回全部请求的闭包。
标签属于该层、标签互异及所有请求码存在均在证明中构造，无附加前提。

实际子公式抽取和有限反射现已完成：PowerlessSourceOpening 使用原
Substitution 将绑定槽变成有限自由输入，保留原自由参数尾部，证明
变量、值列、环境、公式及新增见证的对应；PowerlessSourceRequests
对原公式递归抽取请求，存在量词取原矩阵，全称量词取否定矩阵，
再对子公式作结构归纳得到双向反射准则。准则不预设任何核心理论。

PowerlessSourceReflection.parameters_l 将每个实际有限类内参数族
放入同一个严格高于给定序数的实际层。exists_l 用 SourceFamily
构造更高真极限层，证明自由参数均在该层，再应用反射准则；返回
所有具有这些自由参数、绑定变量在层内的环境上的双向真值保持。
因此层存在性和参数包含性均不是未证前提。此定理反射的是层次类
相对化后的指定原公式，并非完整环境宇宙的一般反射或全公式初等性。

存在性仍使用完整 PowerlessTheory（含 Collection），不是从任意
Z₂ 模型已有的弱集合背景直接推出。下述类内分离／收集、完整类模型
及公理有限支持层模型已经补齐，但一般逐层部分真值正确性、有限稳定对、
实际 BM4 算术程序与任意下降实数对应、目标保持的 Z₂ 推导传输
仍未完成；不能用当前有限反射替代这些终局环节。

## 层次类内的分离、收集与基本闭包

PowerlessClassSeparation.exists_l 对指定原公式的类相对化分离构造
真实类内子集。先反射“属于输入集合且满足该公式”的合取，再在
反射层的真实后继中调用既有原源覆盖。正反向成员规格同时核验；
逆向使用层传递性。输入集合由实际自由参数项给出，所有自由参数
确在类内；这不是把环境模型的分离存在性直接当作类内存在性。

PowerlessClassCollection.exists_l 甚至覆盖部分定义的类内见证请求。
打开实际原二绑定变量矩阵，取高于输入集合所在层的见证闭包层，
并以该层本身作为收集集。PowerlessClassBasic.stage_member_l 经
实际后继方程证明收集集属于类；不预设选择见证函数，也不要求
其他环境参数都在类内。普通全域收集是其直接特例。

PowerlessClassBasic 同时证明共同容纳层、类传递性、全部内部序数
归属、ω/e/T/三个标签归属、空集、配对和并集闭包。分离中所用的
类成员结构与既有集合成员结构通过逐值关系解释相等接线，不改变
旧成员结构定义；HierarchyClass.lift_env_l 核验环境提升的另一方向。

上述装配现已完成：SourceParameters 在 SourceOpening.binding_m 上
提升一／两次 Substitution.liftBound，仅打开参数槽并保留见证次序；
SourcePadding 增加七个实际自由参数 A、三个标签、T、e、ω。
ClassComprehension 对任意原公式及环境证明分离／收集；ClassAxioms
验证基本公理。ClassCore.models_l 接回任意 Project 模式，证明实际
层次类是完整 PowerlessTheory 模型，不只是若干公理样本。

ClassFiniteSupport.models_l 将任意有限核心闭句列表的合取在类中
反射，得到任意指定序数之上的真极限层模型，并通过结构相等返回
既有 MemberStructure。可对 OracleSupport.support_m B 的 sentences
及 subset 实例化，不再假定小层满足该支持。下一步需将其真正用于
部分真值正确性及有限稳定对构造。环境完整 Core 仍是显式前提；
弱集合模型到所需收集背景的目标保持解释依然未完成。

文献边界复核：Gitman–Matthews 的《ZFC without Power Set II》定理 2.1
说明带 Collection 的无幂集集合论上，一般反射模式与 DCω 模式等价，
不能把一般反射直接加入当前核心。当前构造只关闭层次类中的指定见证。
来源：https://arxiv.org/html/2206.06220 。Kanovei–Lyubetsky 的 2022 年
作者预印本第 12 节、定理 9 指出经首个 gap 以下的构造树可取得含
Collection 的解释；这是后续解释路线的文献线索，不是本库已完成的
解释或 BMS 目标保持定理。该预印本的参考文献编号尚未填全。
来源：https://www.preprints.org/manuscript/202212.0255/v1/download 。

## 验证检查点

第一层匹配极性双向正确性与实际层存在性检查点：默认构建 2297
jobs；原终局、有限层 79、三阶 2988（62 个无规模界出口）、全桥
8480 声明审计通过，仅三项标准公理。七个本轮 Lean 文件两树哈希
匹配，450 条旧警告文字及次数不变，163 冻结资源不变；禁止项及
差异检查通过。日志 bms-partial-first-*，独立模块另见
bms-quantifier-parameters-module、bms-partial-exists-module、
bms-partial-quantifier-module、bms-partial-bounded-introduction-module、
bms-partial-bounded-progress-module、bms-partial-first-module、
bms-truth-first-stage-module。无遗留构建，未提交推送；未重跑根工程、
二阶／BMSTools 专门审计或远端 CI。任意有限层及 Z₂ 终局仍未完成。

零层参数推广、有界/同码升层及实际与非推进检查点：默认构建 2295
jobs；原终局、有限层 79、三阶 2953（62 个无规模界出口）、全桥
8445 声明审计通过，只允许三项标准公理。九个本轮 Lean 文件两树
哈希匹配，450 条旧警告文字及次数不变，163 冻结资源不变；禁止项
扫描和差异检查通过。日志 bms-partial-boolean-*。无遗留构建，未
提交推送，未重跑根工程、二阶／BMSTools 专门审计或远端 CI。
原接受公式的无核心参数语义及与非推进已证明；量词推进和 Z₂ 终局
仍未完成。当前额度停止线为剩余不超过 40%。

局部规则有限支持和内部完备性正文检查点：默认构建 2290 jobs；
原终局、有限层 79、三阶 2901（62 个无规模界出口）、全桥 8393
声明审计通过，仅三项标准公理。七个本轮 Lean 文件两树哈希一致；
450 条旧警告文字及次数不变，163 冻结旧资源不变，差异／禁止项检查
通过。日志 bms-oracle-introduction-*；未重跑根工程、二阶／BMSTools
专门审计或远端 CI。第一层构造子推进仍未完成，不能据此声称 Z₂ 终局。

零层真值与第一后继可靠性检查点：默认构建 2286 jobs；原终局、
有限层 79、三阶 2845（62 个无规模界出口）、全桥 8337 声明审计通过。
只允许 propext、Classical.choice、Quot.sound。六个本轮 Lean 文件
两树哈希一致，450 条旧警告文字和次数不变，163 冻结资源不变，
差异及禁止项检查通过。日志 outputs/bms-truth-stage-*；独立模块日志
另见 bms-truth-introduction-module、bms-partial-truth-zero-module、
bms-partial-truth-one-module。无遗留构建，未提交推送；未重跑根工程、
二阶／BMSTools 专门审计或远端 CI。第一层完备性、一般层号归纳、
有限稳定对及 Z₂ 目标保持均未完成。

完整类模型与有限支持检查点：默认构建 2282 jobs；原终局、有限层
79、三阶 2824（62 个无规模界出口）、全桥 8316 声明审计通过。
只允许 propext、Classical.choice、Quot.sound。九个本轮 Lean 文件
两树哈希匹配，450 条旧警告文字与次数不变，163 冻结资源不变，
差异及禁止项检查通过。日志 outputs/bms-class-core-*。无遗留构建；
未重跑根工程、二阶／BMSTools 专门审计或远端 CI，未提交推送。
完整类模型已完成，但固定行数 Z₂ 终局仍未完成。

类内集合闭包检查点：默认构建 2276 jobs；原终局、有限层 79、
三阶 2784（62 个无规模界出口）、全桥 8276 个声明审计通过。
只允许原三项标准公理。六个本轮新增／改动 Lean 文件两树哈希一致，
450 条历史警告文字与重复次数逐项相同，163 个冻结资源不变，
差异和禁止项扫描通过。日志前缀 outputs/bms-class-closure-*；
独立模块日志 bms-class-separation-module.log、bms-class-collection-module.log、
bms-class-basic-module.log（最后一个也核验收集对基本闭包的复用）。
无遗留构建；未重跑根工程、二阶／BMSTools 专门审计或远端 CI，
未提交推送。完整类模型和固定行数 Z₂ 终局仍未完成。

实际子公式反射检查点：默认构建 2273 jobs；原终局、有限层 79、
三阶 2766（62 个无规模界出口）、全桥 8258 个声明审计通过。
只允许 propext、Classical.choice、Quot.sound。五个本轮新增／改动
Lean 文件两树哈希一致，163 个冻结资源不变，差异和禁止项检查通过。
450 条历史警告文字和重复次数一致，已按序排序核对，不要求输出顺序相同。
日志前缀 outputs/bms-source-reflection-*；Opening 与 Requests 独立
构建日志另见 bms-source-opening-module.log、bms-source-requests-module.log。
全桥审计首次使用错误相对路径而未启动，改用工作区 outputs 下真实
绝对路径后执行成功。没有遗留构建；未重跑根工程、二阶／BMSTools
专门审计或远端 CI，未提交推送。固定行数 Z₂ 目标仍在进行。

任意有限元数与共同闭包检查点：默认构建 2270 jobs；原终局、有限层
79、三阶 2719（62 个无规模界出口）、全桥 8211 个声明审计通过。
四个本轮新增／改动 Lean 文件两树哈希一致；450 条历史警告的内容与
次数完全相同，输出顺序有变化（已排序后逐行核对，保留重复次数）。
163 个冻结资源不变，差异及禁止项扫描通过。日志前缀
outputs/bms-source-family-*。无遗留构建；未重跑根工程、二阶／BMSTools
专门审计及远端 CI，未提交推送，目标仍未完成。

实际类接入与双输入编码检查点：默认构建 2268 jobs；原终局、有限层
79、三阶 2666（62 个无规模界出口）、全桥 8158 个声明审计通过。
四个本轮新增／改动 Lean 文件两树哈希一致；450 条历史警告逐行不变，
163 个冻结资源不变，差异及禁止项扫描通过。日志前缀
outputs/bms-source-pack-*。无遗留构建；根工程、二阶／BMSTools 专门
审计及远端 CI 未重跑，未提交推送。目标仍未完成。

原公式类相对化检查点：完整默认构建 2266 jobs；原终局、有限层 79、
三阶 2642（62 个无规模界出口）、全桥 8134 个声明审计通过。
三个本轮新增／改动 Lean 文件两树哈希一致，450 条历史警告逐行不变，
163 个冻结资源不变；差异及禁止项扫描通过。日志前缀
outputs/bms-source-class-*。无遗留构建；根工程、二阶／BMSTools 专门
审计及远端 CI 未重跑，未提交推送。仍未完成有限反射或 Z₂ 终局。

层次内见证闭包检查点：完整默认构建 2265 jobs，原终局、有限层 79、
三阶 2616（62 个无规模界出口）、全桥 8108 个声明审计通过。
六个本轮新增／改动 Lean 文件两树哈希一致，450 条历史警告逐行不变，
163 个冻结资源不变，差异及新增／修改模块禁止项扫描通过。
日志前缀 outputs/bms-source-domain-*。无遗留构建；未重跑根工程、
二阶专门审计、BMSTools 专门审计或远端 CI，未提交推送。目标仍未完成。

固定源公式见证闭包检查点：默认构建 2264 jobs；最终命名修正后聚合目标
构建 2258 jobs；
原终局、有限层 79、三阶 2607（62 个无规模界出口）、全桥 8099 个声明
的审计通过。七个本轮新增／改动 Lean 文件两树哈希一致；450 条历史
警告逐行不变，163 个冻结资源不变，差异和新增模块禁止项扫描通过。
日志前缀 outputs/bms-source-witness-final-*。未重跑根工程、二阶专门审计、
BMSTools 专门审计或远端 CI；未提交推送。这不是 Z₂ 目标完成的声明。

部分真值与低层公式支持检查点：完整构建 2259 jobs；原终局 AxiomAudit、
有限层 79、三阶 2558（62 个无规模界出口）、全桥 8050 个声明的审计通过。
只允许原三项标准 Lean 公理；450 条历史警告逐行不变。八个本轮新增／
改动 Lean 文件两树哈希一致，163 个冻结资源不变，差异／禁止项检查通过。
日志前缀 outputs/bms-oracle-support-*。前一检查点为 2258 jobs／三阶 2539／
全桥 8031，日志前缀 outputs/bms-partial-truth-*。本轮未重跑根工程、
二阶专门审计、BMSTools 专门审计或远端 CI；未提交推送，目标仍未完成。



证书闭包及有限支持检查点：完整构建 2253 jobs；原终局 AxiomAudit、
有限层 FiniteBoundaryAudit、三阶 2467 个声明（62 个无规模界出口）、
全桥 7959 个声明审计全部通过。450 条历史警告逐行不变；四个本轮
新增／改动 Lean 文件与短路径验证树哈希一致，差异及禁止项检查通过。
日志前缀 outputs/bms-truth-support-*；前一闭包检查点为
2252 jobs／三阶 2455／全桥 7947，日志前缀 outputs/bms-truth-closure-*。
此次没有重跑根工程、二阶专门审计、BMSTools 专门审计或远端 CI，未推送。

全局边界检查点：修复命名冲突后的完整构建 2251 jobs；三阶入口
2422 个声明、62 个无规模界出口、全桥 7914 个声明审计全部通过。
原 PowerlessStableBoundary 与 HEAD 无文本差异。日志前缀
outputs/bms-global-boundary-*；bms-internal-boundary-* 保留为失败记录。

内部有限链检查点：完整默认构建 2250 jobs；三阶入口审计 2419 个声明，
62 个无规模界出口检查通过；全桥审计 7911 个声明通过。
新增模块五个公开定理均已编译，450 条原警告逐行不变，禁止项扫描无命中。
日志前缀 outputs/bms-internal-chain-*。这些公理审计只检查 Lean 基础公理，
不表示已经消去定理中的 PowerlessTheory 或延长条件。

直接表示检查点：完整默认构建 2249 jobs；有限层 79、二阶 2845、
三阶 2407、工具 3164、全桥 7902 个声明的审计通过，原终局审计通过。
450 条历史警告不变，163 个冻结资源未变。日志前缀为
outputs/bms-fixed-representation-*。此检查点尚不包括随后新增的
PowerlessFiniteChain 聚合导入；该模块的独立检查已通过。

2026-09-14：新模块独立构建通过，完整默认构建 2248 jobs 通过。
原最终定理、有限层 68、二阶 2845、三阶 2407、工具 3164、
全桥 7889 个声明的相应审计均通过；只允许原三项标准 Lean 公理。
有限层导入守卫未发现全层反射或 FinalAssembly。
450 条历史警告逐行不变，163 个冻结资源未变；
本轮三个改动／新增 Lean 文件与短路径验证树哈希一致。
差异与新模块禁止项检查通过。验证日志为工作区 outputs/bms-fixed-height-*。
这些检查不表示已得到 Z₂ 推导；根工程和远端 CI 未重跑。
