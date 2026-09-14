# 有限层稳定边界：实现与验证记录

首次记录：2026-09-12；持续更新至 2026-09-14。源码基点：`57da9d318df393b1ededbc93cd3abc745c8c8675`。
本轮仅本地修改，未提交、未推送；旧的无额外模型参数终局保持不变。

## 数学变化

新增路线证明如下条件结论，`stageStableLt` 与原项目完全相同：

```lean
FiniteStability.pairs_l :=
  ∀ n, ∃ α β : Ordinal, stageStableLt n α β

FiniteStability.wellOrder_l (h : FiniteStability.pairs_l) :
  StrictWellOrder GeneratedArray GeneratedStrictDescent
```

这不是新增公理：逐层存在性是该新定理显式、尚未在弱背景中消去的参数。
原 `bm4_strictWellOrder_l` 与 `bm4_no_infinite_descent_l` 仍不带此参数。

1. `LocalDescent.expands_l` 只规定有界表示在非平凡展开后严格下降，不要求同一框架表示所有种子。
2. `LocalDescent.acc_l` 从任意有界表示推出原数组的 `Acc Step`，连 `Generated` 前提也不需要。
3. `LocalDescent.wf_l` 将各高度种子的可达性沿实际生成规则传递；标签类型可随高度变化。
4. `FiniteStability.least_l` 在已知第 `n` 层稳定对存在时取最小下端点 `σ`。
5. `cutoff_l` 证明 `α < σ` 且 `α <_k β` 蕴涵 `k < n`；不限制 `β`，所以也覆盖 `β = σ` 的单点反射。
6. `seed_l` 对 `h + 3 ≤ n` 使用原有三次单点反射，得到高度 `h` 的种子表示。
7. 对每个 `h` 使用第 `h + 3` 层的局部边界，得到完整 BM4 的条件良序及无无限下降链结论。

证明仍使用实际 `Ordinal` 的良基性、原有可构造层语义及稳定公式数据。
不能将本轮结果称为 `Z₂ ⊢ WO(BM4)`，也不能称为已经在 `T_cc^L` 内证明。
弱理论路线和未完成项见 [SECOND_ORDER_BACKGROUND.md](SECOND_ORDER_BACKGROUND.md)。

第二条路线的纸面审计进一步发现：如果把逐层存在性内部化为完整的统一语义原则，
它会给出无幂集、带收集的集合论任意有限片段的模型，进而在目标背景中推出自身一致性。
因此，本模块是有用的局部化接口，不是已经降到二阶算术强度的证明；下一步必须削弱
它消费的统一稳定对前提。该强度障碍尚未 Lean 形式化，详见上述文档第 5 节。

## 文件边界

| 文件 | 用途 |
| --- | --- |
| `YesMetaZFC/BMS/LocalDescent.lean` | 与序数模型无关的局部下降及全局装配 |
| `ConstructibleBridge/BMSConstructibleBridge/FiniteStageReflection.lean` | 从旧种子文件原样抽出的三个共享有限反射定理 |
| `ConstructibleBridge/BMSConstructibleBridge/FiniteStableBoundary.lean` | 有限边界、统一截断、局部种子及条件终局 |
| `ConstructibleBridge/BMSConstructibleBridge/FiniteBoundaryAudit.lean` | 新路线的独立导入图及公理守卫 |

移动的三个定理为 `globalFiniteReflection_l`、`boundedFiniteReflection_l`、
`exists_reflectedSingleton_l`；名称、签名和证明体保留。旧种子文件改为导入共享模块。
新文件和新定理采用宿主层 `_l` 后缀及数学局部变量；本轮不进行旧接口的批量命名迁移。

独立审计不能导入桥接总入口，因为总入口有意保留旧的全反射证明。
审计明确禁止新路线导入 `ExternalFullReflection`、`NativeStageReflection`、
`NativeStableBoundary`、`SeedConstruction` 或 `FinalAssembly`，并检查三个新增证明模块
所有声明的传递公理依赖。该守卫不等于对对象理论强度的形式化分析。

## 验证环境与命令

根工程保持 Lean 4.33.1；桥接保持 Lean 4.33.0-rc1。
所有 Lean 构建串行运行，`LEAN_NUM_THREADS=1`，不修改依赖锁文件。

原长路径检出在未改动的依赖模块 `RudimentaryStackProgramOrderRepresented` 写出
`.olean.server` 时失败。目录联接被 Lake 解析回长路径，因此改用独立的短路径验证工作树，
复用锁定依赖缓存，并逐文件核对本次源码。没有关闭检查，也没有改动该第三方模块。

完整检查仍可运行：

```sh
bash scripts/check-all.sh
```

新增的独立检查是：

```sh
cd ConstructibleBridge
lake env lean BMSConstructibleBridge/FiniteBoundaryAudit.lean
```

本轮开始时根 BMS 入口的基线构建通过（42 jobs）。新增 `LocalDescent` 的根工程
定向构建通过（14 jobs，零警告）。最终检查结果如下，不以旧缓存或纸面检查替代。

## 第一轮最终检查

以下检查已完成。本次 Windows 验证使用与脚本相同范围的串行调用；根工程在主检出，
桥接在 `C:/Users/17857/Documents/Codex/bm4v` 验证工作树中运行。使用锁定缓存进行
全量目标检查，不宣称从空缓存重建，也不宣称远端 CI 已运行。

| 检查 | 结果 |
| --- | --- |
| 根工程全部 827 个模块及 `prove_auto_sweep`，`--wfail` | 通过，零警告 |
| `FiniteStableBoundary` 定向构建 | 通过，1520 jobs；新增证明模块零警告 |
| 桥接总入口 `BMSConstructibleBridge` | 通过，1529 jobs；保留旧模块的 450 条警告 |
| 旧终局两个定理的 `AxiomAudit.lean` | 通过，预期三项标准公理 |
| 新路线 `FiniteBoundaryAudit.lean` | 通过，41 个声明；禁止导入模块均未出现 |
| 桥接全声明传递公理检查 | 通过，2690 个声明；仅 `propext`、`Classical.choice`、`Quot.sound` |
| 7 个改动／新增 Lean 源码在两树中的 SHA-256 | 全部相同 |
| 两树各 10 个桥接 Git 依赖 | 全部匹配锁定提交，排除缓存后源码无修改 |
| 根配置、桥接配置 | 根配置逐字节相同；桥接配置仅 LF／CRLF 差异，内容与版本相同 |
| 三个共享反射定理 | 与原文件中的签名和证明体一致，仅移动位置 |
| 禁用证明占位／新增公理扫描、`git diff --check`、检查脚本语法 | 通过 |

新审计首次运行暴露了计数变量的类型推断错误，补充 `: Nat` 后，整套新旧审计重新通过；
未放宽公理白名单或导入守卫。原 `FinalAssembly.lean` 未修改。

本地完整执行日志在主仓库同级的 `outputs/`：`bms-finite-root.log`、
`bms-finite-bridge.log`、`bms-finite-audits.log`。它们是本地验证输出，不在本轮发布范围。

本轮未提交、未推送。已验证的是新增的**条件良序证明与接口隔离**；
第二条路线的一致性障碍仍是独立的纸面推导，不属于这 2690 个声明的机器证明。

## 第二轮：二阶呈现、有限模式与对角展开

同日继续实现，仍基于本文开头的提交，仅在本地修改。没有修改原终局或两个
工程的工具链、依赖清单；桥接继续使用同一短路径树，所有构建和审计串行运行。

| 新文件 | 已证内容及边界 |
| --- | --- |
| `YesMetaZFC/BMS/FinitePatternDescent.lean` | 自动有限支撑、实际形状输入反射到表示下降、逐高度装配；保留标签良基性与见证存在前提 |
| `YesMetaZFC/BMS/SeedExpansion.lean` | 显式对角数组、seed 展开公式、整个对角族与高一层 seed 的可达性等价 |
| `BMSConstructibleBridge/ArithmeticPresentation.lean` | 总解码、满射、有限检查器，以及原一步关系／良基性／任意下降链的精确对应 |
| `BMSConstructibleBridge/SecondOrderPresentation.lean` | 单个 `Set Nat` 量词的目标，与原无无限下降链精确等价 |
| `BMSConstructibleBridge/SecondOrderAudit.lean` | 独立导入隔离及上述四个证明模块全部声明的公理检查 |

表中后三个文件位于 `ConstructibleBridge/`。新的独立审计禁止导入任何
`ConstructibleUniverse` 模块、`Mathlib.SetTheory.Ordinal` 模块，以及除两个呈现模块
以外的桥接语义模块。它已接入检查脚本和 CI 配置，但本轮没有推送，故没有远端 CI 结果。

独立语义复核确认：反射接口没有把 `Acc`、BM4 良序性或严格表示下降作为输入假设；
单集合图涵盖任意链，而非仅可计算链；重复编码不会制造同数组之间的伪下降。
编码上的关系不保证线性；算术呈现尚不是对象 `Z₂` 公式或原始递归证书。
数学细节及下一步见 [SECOND_ORDER_BACKGROUND.md，第 10 节](SECOND_ORDER_BACKGROUND.md#10-第二轮真正推进到哪里)。

第二轮最终检查均已通过：

| 检查 | 结果 |
| --- | --- |
| 根工程全部 829 个模块及 `prove_auto_sweep`，`--wfail` | 通过，零警告 |
| 桥接总入口 | 通过，1533 jobs；旧模块仍有 450 条警告，本轮新增证明模块零警告 |
| 旧终局两个定理的 `AxiomAudit.lean` | 通过，原预期标准公理依赖未变 |
| 第一轮 `FiniteBoundaryAudit.lean` | 通过，41 个声明及导入守卫 |
| 第二轮 `SecondOrderAudit.lean` | 通过，79 个声明及导入守卫 |
| 桥接全声明传递公理检查 | 通过，2729 个声明；仅三项标准公理 |
| 两轮累计 12 个改动／新增 Lean 文件在主树与短路径树的 SHA-256 | 全部相同 |
| 禁用证明占位／新增公理扫描、`git diff --check`、检查脚本语法 | 通过 |

本轮两项根模块还分别通过 Lean 4.33.1 的定向 `--wfail` 构建，并在桥接的
Lean 4.33.0-rc1 中重新编译。所有完整目标检查复用锁定缓存，不宣称空缓存重建。
日志为同级 `outputs/bms-z2-root.log`、`bms-z2-bridge.log`、`bms-z2-audits.log`。

本轮没有修改 `FinalAssembly.lean`，没有新增项目公理，没有提交或推送。
新增的公理审计证明依赖符合仓库标准，**不证明其理论强度已降至 `Z₂`**。

## 第三轮：当前高度分解、规范代码及基础递归证书

仍基于同一提交在本地继续研究，没有提交或推送。
新增 `YesMetaZFC/BMS/HeightDescent.lean` 与桥接 `PrimitiveCoding.lean`，扩展
`ArithmeticPresentation.lean`、`SecondOrderPresentation.lean` 及独立审计。
`Reference.lean` 仅增加公开的支撑高度递推定理，原计算定义和已有定理未改。

本轮数学交付：展开高度非增；全体一步良基性与全部当前高度纤维良基性等价；
任意无限链具有固定高度尾部；零高度纤维无条件良基；控制高度 `0,…,h` 的纤维
足以控制高一层 seed 的全部后继。正高度纤维的良基性仍是待证数学命题。

算术呈现改用可判定数组等式的最小自然数代码，证明还原、最小性、单射、规范化
幂等和检查结果保持，给出规范代码子类型与生成数组的实际双射。原链提升不再
任意选择每个数组的代码；不声称全工程消除了 `Classical.choice`。

原始递归证书已针对实际函数及实际编码构造：轨迹编解码、坐标查询、支撑高度、
裁剪高度、裁剪、seed、有界最大值搜索、零行 parent。高行 parent、ancestor、
完整展开及最终检查器仍未获得该证书；对象算术内的总性与句法表示也未完成。
`SecondOrderAudit` 扩大检查范围并要求本轮关键定理确实存在，继续禁止语义序数模块。

验收仍采用精确的两套工具链、串行构建和短路径桥接树，未关闭任何新检查。
数学规格与证明债务详见 [SECOND_ORDER_BACKGROUND.md，第 11 节](SECOND_ORDER_BACKGROUND.md#11-第三轮当前高度分层及第一批原始递归证书)。

第三轮最终检查全部通过：

| 检查 | 结果 |
| --- | --- |
| 根工程全部 830 个模块及 `prove_auto_sweep`，`--wfail` | 通过，零警告 |
| 桥接总入口 | 通过，1542 jobs；旧模块 450 条警告，本轮新增或扩展模块零警告 |
| 原终局两个定理的 `AxiomAudit.lean` | 通过，原预期公理依赖不变 |
| `FiniteBoundaryAudit.lean` | 通过，41 个声明及导入隔离 |
| 扩展后的 `SecondOrderAudit.lean` | 通过，144 个声明；无可构造语义或 `Ordinal` 模块导入 |
| 桥接全部声明传递公理检查 | 通过，2759 个声明；仅 `propext`、`Classical.choice`、`Quot.sound` |
| 三轮累计 15 个改动／新增 Lean 文件的两树 SHA-256 | 全部相同 |
| 根与桥接 Lake 配置、工具链及锁文件 | 内容相同，忽略原有 LF／CRLF 差异；版本未改 |
| 禁用证明标记扫描、`git diff --check`、脚本语法 | 通过 |

基础递推引理触发了旧桥接公式模块的重新检查，所以本轮桥接耗时主要是旧依赖重建。
首次从短路径目录收集主树改动清单遭遇 Git 目录信任检查，未完成源码同步；该次
结果没有作为最终验收。随后从主树取得完整清单、同步并核对 15 文件哈希，再重新
完成根工程、桥接总入口及全部审计。以后跨目录收集清单必须检查 Git 退出码和非空性。

最终日志在同级 `outputs/`：`bms-z2-height-root.log`、`bms-z2-height-bridge.log`、
`bms-z2-height-audits.log`。验证复用锁定缓存，不宣称空缓存重建或远端 CI 通过。
`FinalAssembly.lean` 保持不变，全部修改仍未提交、未推送。

本轮交付的是分层归约、零高度基例、规范代码及部分基础函数的原始递归证书。
不将任何上述公理检查、宿主等价或局部可达性宣称为已经完成的 `Z₂` 内良序证明。

## 第四轮：实际算法的纯二阶呈现、局部反射和树码传输

日期：2026-09-12。基点仍为 `57da9d318df393b1ededbc93cd3abc745c8c8675`，
分支 `refactor/bms-slimming`。四轮研究改动均未提交或推送。

本轮完成第三轮列出的全部实际算法原始递归证书，包括任意行 parent、祖先、
复制块、完整展开、轨迹解码、检查器和规范化。它们没有改变原 BM4 计算规则。
另完成单集合可数反射背景到逐高度种子可达性、逐高度句与原完整目标的等价。

纯语言部分不是只检查宿主谓词名称：`PrimitiveHistory` 证明实际有限 β 历史的
语义，`PrimitiveFormulas.primrec_l` 覆盖全部七个 `Nat.Primrec` 构造子，
`PureSecondOrder.formula_l` 据此给出原 BM4 逐高度目标的纯 `Π¹₁` 公式。
纯语言检查排除了配对、seed、展开等额外符号及矩阵内部的集合量词。

树码部分新增实际最大双模拟、单实数见证编码、完整匹配方程和自然数最小见证的
逐步链提升。指定根的外部无路径性质可直接排除换码成员下降；不借用模型内部
无下降链的向外绝对性。可计算预算部分按实际语法秩产生等级，证明具名边、
低级 ambient 边和有限存在闭包的复杂度界，未替换旧稳定关系。

本轮最终验收结果如下，所有构建和审计串行进行。

| 检查 | 结果 |
| --- | --- |
| 根工程 830 个模块及 `prove_auto_sweep`，Lean 4.33.1，`--wfail` | 通过，零 Lean 警告 |
| 桥接总入口，Lean 4.33.0-rc1 | 通过，1558 jobs；旧模块 450 条警告，本轮新增模块零警告 |
| 原终局 `AxiomAudit.lean` | 通过，两项原定理预期公理集合不变 |
| `FiniteBoundaryAudit.lean` | 通过，63 个声明；包括新复杂度预算，禁止旧全层反射导入 |
| `SecondOrderAudit.lean` | 通过，704 个声明；没有可构造语义或 `Ordinal` 导入 |
| 桥接全声明传递公理检查 | 通过，3337 个声明；仅 `propext`、`Classical.choice`、`Quot.sound` |
| 主树与短路径验证树的 Lean 源码 SHA-256 | 累计 26 个改动或新增文件全部相同 |
| 两工程的工具链、Lake 配置及锁文件 | 原文件未改；两树六个配置忽略原有换行差异后相同 |
| `FinalAssembly.lean`、禁用证明标记、脚本语法及 `git diff --check` | 原终局未改，其余检查均通过 |

`TreeTransfer.pullback_l` 与 `Bisimulation.unfold_l` 的独立检查均显示无公理
依赖；`EffectiveStability.level_m` 不依赖 `Classical.choice`，但仍依赖
`propext` 与 `Quot.sound`，不将其误报为完全无公理。其他新定理均符合上述
三项标准可信基，未新增项目公理或证明占位。

内存处理：最初直接展开固定公式秩的预算证明触发高内存，已中止该次验证。
随后用 2048 MB 限额定位到两个闭式等级转换；先对抽象初值证明，再代入实际
初值，消除了具体巨型秩的反复归约。修正后的预算模块约 6 秒编译通过。
没有提高心跳上限、关闭 linter 或降低可信标准。

最终依据只取同级 `outputs/` 中三个新日志：`bms-z2-round4-root.log`、
`bms-z2-round4-bridge.log`、`bms-z2-round4-audits.log`。旧带 `final` 字样的
中间日志可能保留前一检查轮的输出，不用其累计计数作本轮最终证据。
所有完整检查复用锁定缓存，不宣称空缓存重建或远端 CI 已通过。

**尚未完成降低证明背景的对象理论终局。** 已实现的是纯公式、算法证书、
可数反射的相对证明、复杂度预算及树码链传输。`Z₂` 内的固定高度推导、
实际证明生成器、KL 解释的具体集合论接线，以及文档第 12 节 `(G)` 的对象
核验仍未完成。`Z₂ + RFN_{Π¹₁}(Z₂)` 目前是候选纸面后备上界，不是本轮已
证明的 Lean 背景归约定理。完整边界见 `SECOND_ORDER_BACKGROUND.md` 第 12 节。

## 第五轮：对象公理、完整公式归纳与闭项推导

日期：2026-09-12；基点及分支不变，所有研究改动仍在本地、未提交或推送。
新增 `SecondOrderArithmetic`：明确的两排序对象公理、完整理解、标准模型、
空集存在推导、完整公式归纳推导及直接归纳规则。另有任意数码加乘和不等式
推导、对象左零律，以及纯闭算术项的求值等式推导。范围及限制见背景文档第 13 节。

本轮最终串行验收如下。

| 检查 | 结果 |
| --- | --- |
| 根工程 830 个模块及 `prove_auto_sweep`，Lean 4.33.1，`--wfail` | 通过，零 Lean 警告 |
| 桥接总入口，Lean 4.33.0-rc1 | 通过，1573 jobs；旧警告 450 条，本轮新增模块零警告 |
| 原终局 `AxiomAudit.lean` | 通过，两项原终局的预期公理集合未变 |
| `FiniteBoundaryAudit.lean` | 通过，63 个声明 |
| `SecondOrderAudit.lean` | 通过，898 个声明；无可构造语义或 `Ordinal` 导入 |
| 全桥接传递公理审计 | 通过，3531 个声明；仅三项标准公理 |
| 主树／短路径验证树源码 SHA-256 | 27 个改动及新增 Lean 文件全部相同 |
| 工具链、Lake 配置及锁文件 | 原文件未改；六个配置忽略原有换行差异后相同 |
| 原终局、禁用标记、脚本语法、`git diff --check` | 原终局未改，其余检查通过 |

`induction_derives_m` 的依赖为 `propext`、`Quot.sound`；`eval_derives_m`
及元层一致性核验的依赖还含 `Classical.choice`。没有新增 Lean 公理或占位证明。
前者是直接的对象逻辑推导，不是从标准模型真值或语义完备性反推可证性。
后者的宿主求值接口及标准可信基也不构成对象算术中的统一算法总性证明。

新增等词推导依赖的初次直接检查遇到旧版本 `.olean` 头不匹配；随后由桥接
Lake 工程按锁定工具链串行重建该依赖，未修改工具链、未删除缓存。最终验收
使用修正后的完整构建，不采用该失败的中间检查。

日志只取同级 `outputs/bms-z2-round5-root.log`、`bms-z2-round5-bridge.log`、
`bms-z2-round5-audits.log`。仍复用锁定缓存，不宣称空缓存构建或远端 CI 通过。
第五轮前半程的 `bms-z2-object-*` 日志只覆盖当时的 3450 个桥接声明，不能替代
本轮最终 3531 个声明的记录。

用户新增的停止约束按常规 Codex **剩余额度 50%** 执行：每个小阶段读取实时
额度，接近阈值时保留整理空间，到阈值结束本次工作，不自动重置额度或上传。
本轮验收时读取为已用 23%、剩余 77%，因此继续下一项实质证明义务。

## 第六轮首段：显式原始递归程序

新增 `PrimitiveProgram` 的实际程序数据、求值、纯公式图编译和语义证书，另有
恒等、常数、加法、乘法的具体程序及全输入正确性定理。单模块以 `--wfail`
核验通过，889 jobs，零警告。实际 BM4 算法全体的程序转换与对象总性仍未完成。

串行核验：桥接总入口 1574 jobs；旧警告 450、新模块零警告；原终局公理检查
通过；有限层 63、独立二阶 1051、全桥接 3684 个声明的审计通过，仍仅三项
标准公理。主树与验证树的累计 28 个 Lean 源文件哈希相同。根工程源文件及
全部工具链配置未改，沿用刚完成的第五轮根工程 830 模块及 sweep 零警告结果。

证据为 `outputs/bms-z2-program-bridge.log`、`bms-z2-program-audits.log`。
程序的图证书与乘法正确性均仍有 `Classical.choice` 标准依赖；不误报为无公理。
当前额度读取为剩余 76%，继续工作；该记录不表示已经完成背景降低或已经推送。

## 第六轮续：纯闭句、图码解释及实际域公式

日期：2026-09-13；源码基点和分支不变，全部研究改动仍在本地，未提交或推送。
完成 `PureSecondOrder` 自身的数码闭句接线；推广跨图双模拟并保留单图特例。
新增 `CountableGraph`、`GraphNaturals`、`GraphClosure`、`GraphFunctions`、
`GraphCountability`、`GraphSyntax`、`GraphDomain`。逐项数学范围及对象层缺口
见背景文档第 15—17 节，不能将这些语义构造和公式呈现报告为 `(G)` 完成。

| 检查 | 最新结果 |
| --- | --- |
| 根工程 830 个模块及 `prove_auto_sweep`，Lean 4.33.1，`--wfail` | 本日重新通过，零 Lean 警告 |
| 桥接总入口，Lean 4.33.0-rc1 | 1581 jobs 通过；450 条旧警告与前一基线逐条相同，新模块零警告 |
| 原终局 `AxiomAudit.lean` | 通过，原终局与公理集合未变 |
| `FiniteBoundaryAudit.lean` | 63 个声明通过 |
| `SecondOrderAudit.lean` | 1275 个声明通过；无可构造语义或 `Ordinal` 导入 |
| 全桥接声明传递公理检查 | 3908 个声明通过；仅三项标准公理 |
| 主树／短路径验证树 | 累计 35 个改动或新增 Lean 文件 SHA-256 相同 |
| 两工程工具链、Lake 配置及锁文件 | 原文件未改；六个配置在两树忽略换行差异后相同 |
| 禁用证明标记、原终局、`git diff --check` | 无禁用标记、原终局未改、差异检查通过 |

图域的 `ext_l`、`wellFounded_l` 与跨图 `Bisimulation.unfold_l` 不依赖公理。
分离语义、自然数无穷实例与节点坍缩唯一性只依赖 `propext`；内部函数图、
可数性和纯公式语义等结果仍在三项标准可信基内，不误报为全部无公理。

验证严格串行。根工程与桥接使用不同工具链，因此中间切换后由 Lake 按锁定
版本重建了共享的相关依赖，没有改工具链或删缓存。公式语义检查中一次整体
展开触发默认心跳上限，已改为逐个语法构造子的语义重写；未提高心跳限制、
未关闭 linter，也没有新增证明占位。

最新证据仅取 `outputs/bms-z2-round6-root.log`、`bms-z2-domain-bridge.log`、
`bms-z2-domain-audits.log`。同日较早的 `bms-z2-round6-bridge/audits.log`
只覆盖 3804 个桥接声明，`bms-z2-graphs-bridge/audits.log` 覆盖 3838 个声明，
都不替代最新 3908 个声明的审计。所有验证复用锁定缓存，不宣称空缓存或远端
CI 已通过。

## 第七轮首段：全公式语义解释

新增 `GraphQuotient`、`GraphTranslation`、`GraphInterpretation`，将原纯集合论
类型化语法完整翻译到已有双排序语法，核验全部公式的标准语义，不改变原 BM4
主定理。商结构处理真正的源等词，量词双向覆盖实际代码和全部商元素。

串行验收：桥接 1584 jobs；450 条旧警告与上一基线相同，新模块零警告；
原终局公理检查通过；有限层 63、独立二阶 1391、全桥接 4024 个声明审计通过。
两树 38 个改动或新增 Lean 文件哈希相同。根工程未再改，沿用本日第六轮
830 个模块与 sweep 的完整零警告构建。`git diff --check` 通过。

本段证据为 `outputs/bms-z2-interpretation-bridge.log` 和
`outputs/bms-z2-interpretation-audits.log`。商良基性依赖 `propext`，完整公式
语义仍依赖三项标准公理。没有从标准模型真值推断对象可导出性。
本段之后新增的纯替换封闭性模块不包含在这个 4024 声明检查点内。

## 第七轮续：纯语言封闭与分离选择器

新增 `SecondOrderSubstitution` 和 `GraphSeparation`；完整翻译的纯语言检查、
根数理解／归纳的对象推导、逐变量换码不变性及实际分离选择器均已通过。
数学范围见背景文档第 19 节，仍不把选择器理解推导计作整个分离公理解释。

最新串行验收：桥接 1586 jobs；450 条旧警告逐条不变，新模块零警告；
原终局公理检查通过；有限层 63、独立二阶 1449、全桥接 4082 个声明通过。
两树 40 个 Lean 源文件哈希相同，根工程源及工具链配置未改。
纯替换及新增三个对象模式推导只依赖 `propext`、`Quot.sound`；语义分离还
依赖 `Classical.choice`。没有新增公理、证明占位或放宽检查限制。

日志为 `outputs/bms-z2-separation-bridge.log` 与 `bms-z2-separation-audits.log`。
本段之后的 `SecondOrderModel` 不包含在这个检查点内。额度最新读取为剩余
68%，未到用户要求的 50% 停止阈值，继续处理非标准模型中的解释义务。

## 第八轮首段：任意模型的理解、归纳及算术

新增 `SecondOrderModel`、`SecondOrderNumbers`、`SecondOrderOrder`、
`SecondOrderPairing`。标准性和 β 性都不是这四个模块的前提；模型理解与归纳
明确限制在实际纯公式。完整范围及尚缺的反向编码见背景文档第 20 节。

串行验收：桥接 1590 jobs，原终局公理检查通过；有限层 63、独立二阶 1497、
全桥接 4130 个声明审计通过，仅三项标准公理。两树 44 个改动或新增 Lean
文件哈希相同；六个配置忽略原换行差异后相同，工具链与原终局未改。
`git diff --check` 通过，根源未改，沿用本日根全工程的零警告记录。

本段证据为 `outputs/bms-z2-models-bridge.log` 和 `bms-z2-models-audits.log`。
新增模型语义接口仍依赖标准三项可信基，不误报为无公理。接下来新增的乘法
模块不包含在这个 4130 声明检查点内。最近额度读取为剩余 66%，继续工作。

## 第八轮续：非标准配对与反向投影

新增乘法、有序半环、平方区间和反配对四个模块。模型内部实际公式归纳证明
每个模型数都有唯一配对坐标，并连接原投影模板；没有标准数域或 β 模型前提。
数学范围与仍未完成的 `(G)` 见背景文档第 21 节。

串行验收：桥接 1602 jobs；原终局公理检查通过；有限层 63、独立二阶 1550、
全桥接 4183 个声明通过。450 条旧警告与基线逐条相同，新模块零警告。
两树 48 个改动或新增 Lean 文件 SHA-256 相同，`git diff --check` 通过。
未改根源码、原终局或工具链；沿用本日根全工程的零警告记录。

日志：`outputs/bms-z2-unpairing-bridge.log`、`bms-z2-unpairing-audits.log`。
此后新增的 `SecondOrderRelations` 不属于本检查点。最近额度剩余 64%，未到
50% 停止阈值；全部研究改动继续保留本地，不提交、不推送。

## 第九轮首段：内部关系及根域遗传性

新增 `SecondOrderRelations`、`SecondOrderFunctions`、`SecondOrderDomain`，
实际公式的二元理解、内部函数图的前缀构造及子根域保持全部通过。
原域模板仅公开原全函数正文作为复用接口，公式数学内容不变。

串行验收：桥接 1605 jobs；原终局公理检查通过；有限层 63、独立二阶 1588、
全桥接 4221 个声明通过，仅三项标准公理；450 条原警告逐条不变、新模块零。
两树 51 个改动或新增 Lean 文件哈希相同。根工程与工具链未改，完整根验证
记录仍为本日第六轮。所有验证使用既有锁定缓存，不宣称远端 CI 或空缓存验收。

日志为 `outputs/bms-z2-internal-domain-bridge.log` 和
`bms-z2-internal-domain-audits.log`。后续 `SecondOrderRelationOps` 和
`SecondOrderBisimulation` 不计入这个检查点。额度最近读取剩余 63%，继续工作。

## 第九轮续：任意模型完整公式解释

新增内部关系操作、内部双模拟、内部图码、商结构和完整公式解释五个模块。
全部公式继续使用原翻译；等词、成员、全部交错量词及参数换码均在任意模型
语义下核验，没有内部良基到外部 `Acc` 的转换。

串行验收：桥接 1610 jobs；原终局公理检查通过；有限层 63、独立二阶 1720、
全桥接 4353 个声明通过，仅三项标准公理。450 条旧警告逐条相同、新模块零。
两树 56 个改动或新增 Lean 文件哈希相同，差异检查通过；根源码、终局定理
和工具链不变。根完整验证仍采用本日第六轮记录。

日志为 `outputs/bms-z2-internal-interpretation-bridge.log` 和
`bms-z2-internal-interpretation-audits.log`。随后的固定调度与完备性回传模块
不包含在这一检查点内。额度最近剩余 62%，继续本地研究，未提交或推送。

## 第十轮首段：外延、空集及反配对的实际对象推导

新增 `SecondOrderCompleteness`、`SecondOrderAxioms`，固定签名调度复用上游
通用语法编码。由全模型语义证明回传外延、空集完整翻译和反配对存在的真实
对象推导；仍没有原始递归证明生成器或 `(G)`。

串行验收：桥接 1631 jobs；原终局公理检查通过；有限层 63、独立二阶 1766、
全桥接 4399 个声明通过。450 条原警告逐条不变，新模块零警告；对象推导仍
仅依赖三项标准公理。两树 58 个改动或新增 Lean 文件哈希相同，根源码、
原终局和工具链未改。

证据为 `outputs/bms-z2-object-axioms-bridge.log`、`bms-z2-object-axioms-audits.log`。
此后新增的拼接图、链变换及拼接域模块不计入这个检查点。最近额度剩余 62%。

## 第十轮续：完整分离模式

新增拼接图、内部链变换、拼接域保持、拼接成员语义、任意模型分离构造及完整
分离闭模式回传六个模块。`SecondOrderSeparationAxiom.derives_m` 对任意原
公式和全部有限参数给出真实对象证明，未采用外部 `Acc`。

串行验收：桥接 1640 jobs；原终局公理检查通过；有限层 63、独立二阶 1823、
全桥接 4456 个声明通过，可信基仅三项标准公理。450 条旧警告逐条不变、
新模块零警告；两树 64 个改动或新增 Lean 文件哈希相同，差异检查通过。

日志为 `outputs/bms-z2-object-separation-bridge.log` 和
`bms-z2-object-separation-audits.log`。随后内部自然数序和无穷公理模块不计入
这个检查点。根源码、原终局、工具链以及线上仓库保持不变。

## 第十一轮首段：无穷公理

新增根域闭包、内部自然数图、归纳集及其对象无穷公理四个模块。实际域公式
归纳遍历整个模型数域，不假定所有模型数都由标准自然数表示。

串行验收：桥接 1644 jobs；原终局公理检查通过；有限层 63、独立二阶 1841、
全桥接 4474 个声明通过。450 条旧警告逐条不变、新模块零；两树 68 个改动
或新增 Lean 文件哈希相同。根源码、终局与工具链未改。

日志：`outputs/bms-z2-object-infinity-bridge.log`、`bms-z2-object-infinity-audits.log`。
随后新增的并集模块不计入这个检查点。额度最新读取剩余 61%，继续工作。

## 第十一轮续：并集与配对

新增并集、带标签图、标签域保持及配对四模块，已有完整公理翻译的对象推导。
标签不变性用实际公式归纳涵盖非标准索引；未引入外部良基假设。

串行验收：桥接 1648 jobs；原终局公理检查通过；有限层 63、独立二阶 1878、
全桥接 4511 个声明通过，仅三项标准公理。450 条旧警告逐条相同、新模块零；
两树 72 个改动或新增 Lean 文件哈希相同，差异检查通过。

日志：`outputs/bms-z2-object-pair-union-bridge.log`、
`bms-z2-object-pair-union-audits.log`。后续内部最小元模块不计入此检查点。
根源码、终局与工具链不变，未提交或推送。额度最新剩余 60%，继续工作。

## 第十二轮首段：内部递归与正则公理

新增内部最小元、实数有限历史、完整迭代、图域极小元和正则公理五个模块。
所有模型归纳均以实际公式为正文，没有外部 `Acc` 或集合选择前提。

串行验收：桥接 1653 jobs；原终局公理检查通过；有限层 63、独立二阶 1923、
全桥接 4556 个声明通过，仅三项标准公理。450 条旧警告逐条相同、新模块零；
两树 77 个改动或新增 Lean 文件哈希相同，差异检查通过。

日志：`outputs/bms-z2-object-foundation-bridge.log`、
`bms-z2-object-foundation-audits.log`。随后传递超集模块不计入这一检查点。
原 BM4 终局、根源码、工具链和线上仓库不变；最近额度仍剩余 60%。

## 第十二轮续：传递超集、精确内部自然数及整理论证传输

新增传递超集、内部自然数和弱集合论片段三个模块，并补正则公理的自成员
排除推论。该片段的任意闭句推导均可回传，不包含尚待证明的坍缩或可数性。

串行验收：桥接 1656 jobs；原终局公理检查通过；有限层 63、独立二阶 1957、
全桥接 4590 个声明通过，仅三项标准公理。450 条原警告逐条相同、新模块零；
两树 80 个改动或新增 Lean 文件哈希相同。

日志：`outputs/bms-z2-weak-set-theory-bridge.log`、
`bms-z2-weak-set-theory-audits.log`。后续统一配对层不计入这一检查点。
仍未提交或推送；额度最近剩余 59%，继续工作。

## 第十三轮：完整内部可数性公理

新增统一配对层、有序对规格与坐标唯一性、统一有序对根、同图和跨图关系像、
成员最小编号、集合函数规格、内部注入、最小归纳对象、纯对象模板、ω 模板及
可数性对象公理十二个模块。函数本身为内部集合，不只存在于 Lean 宿主。

串行验收：桥接 1668 jobs；原终局公理检查通过；有限层 63、独立二阶 2098、
全桥接 4731 个声明通过，仅三项标准公理。450 条旧警告逐条相同、新模块零；
两树 92 个改动或新增 Lean 文件哈希相同，差异检查通过。

日志：`outputs/bms-z2-object-countability-bridge.log`、
`bms-z2-object-countability-audits.log`。后续关系对象解码模块不计入这一检查点。
根源码、原终局、工具链及线上仓库不变；额度最近剩余 58%，继续工作。

## 第十四轮：完整 MostColl 与 TMC

新增关系对象解码、内部正则关系、坍缩对象及函数、完整 Mostowski 构造、
纯关系与坍缩模板、MostColl 对象公理及 TMC 整理论证传输十个模块。
MostColl 的场为字面 `dom ∪ ran`，不要求关系外延；完整闭句的原翻译已有
实际对象推导。任意已有 TMC 闭句推导均可传输，不仅是单条公理。

串行验收：桥接 1678 jobs；原终局公理检查通过；有限层 63、独立二阶 2202、
全桥接 4835 个声明通过，仅三项标准公理。450 条旧警告逐条相同、新模块零；
两树 102 个改动或新增 Lean 文件哈希相同，差异检查通过。

日志：`outputs/bms-z2-object-tmc-bridge.log`、`bms-z2-object-tmc-audits.log`。
后续有限编码工作不计入这一检查点。根源码、原终局和工具链保持不变，
未提交或推送。最新额度剩余 57%；BM4 的 `L*` 桥与 PRA `(G)` 仍待完成。

## 第十五轮首段：内部有限数集编码

新增模型带余除法、一般幂函数、二进制幂、纯位公式及有限数集编码五模块。
`SecondOrderFiniteCode.segment_l` 提供全部模型长度上的精确数码，界外为零；
并非只验证标准数或提供外部有限性证书。

串行验收：桥接 1683 jobs；原终局公理检查通过；有限层 63、独立二阶 2262、
全桥接 4895 个声明通过，仅三项标准公理。450 条旧警告逐条相同、新模块零；
两树 107 个改动或新增 Lean 文件哈希相同，差异检查通过。

日志：`outputs/bms-z2-finite-coding-bridge.log`、`bms-z2-finite-coding-audits.log`。
随后内部有限函数值域界模块不计入本检查点。根源码、终局与工具链不变，
未提交或推送；额度最近剩余 57%，继续进行数值有限函数编码。

## 第十五轮续：数值有限函数与对象历史定理

新增有限值域界、数值函数图、纯读取、数值历史、幂图规格及历史对象定理六个
模块。闭句存在量化一个正确幂图，并提供所有模型长度上的数值历史，已经有
实际对象 `Derives`；原 β 编译器及 BM4 的 `(G)` 不在已完成范围。

串行验收：桥接 1689 jobs；原终局公理检查通过；有限层 63、独立二阶 2346、
全桥接 4979 个声明通过，仅三项标准公理。450 条旧警告逐条相同、新模块零；
两树 113 个改动或新增 Lean 文件哈希相同，差异检查通过。

日志：`outputs/bms-z2-number-history-bridge.log`、`bms-z2-number-history-audits.log`。
随后内部实数行模块不计入本检查点。原终局、根源码及工具链保持不变，
未提交或推送；额度最近剩余 56%，继续工作。

## 第十六轮：唯一集合值迭代的对象方案

新增内部实数行、实际集合操作公式、集合值有限历史、唯一迭代及其对象方案
五模块。整张内部迭代图由理解产生，不调用可数集合选择；完整参数闭方案
具有实际对象 `Derives`，全域性与唯一性保留为句中前提。

串行验收：桥接 1694 jobs；原终局公理检查通过；有限层 63、独立二阶 2439、
全桥接 5072 个声明通过，仅三项标准公理。450 条旧警告逐条相同、新模块零；
两树 118 个改动或新增 Lean 文件哈希相同，差异检查通过。

日志：`outputs/bms-z2-set-iteration-bridge.log`、`bms-z2-set-iteration-audits.log`。
根源码、原 BM4 终局和工具链不变，未提交或推送。统一内部满足关系、`Def`、
`L*` 及 BM4 的 PRA `(G)` 仍待完成；额度最近剩余 55%。

## 第十七轮首段：内部赋值与节点编码

新增有限赋值、赋值及前插公式、内部节点编码三个模块。前插保留全部旧位置
并检查界外无边；节点及嵌套子节点严格下降，但尚未宣称完整内部语法或满足
关系完成。

串行验收：桥接 1697 jobs；原终局公理检查通过；有限层 63、独立二阶 2485、
全桥接 5118 个声明通过，仅三项标准公理。450 条旧警告逐条相同、新模块零；
两树 121 个改动或新增 Lean 文件哈希相同，差异检查通过。

日志：`outputs/bms-z2-assignment-codes-bridge.log`、`bms-z2-assignment-codes-audits.log`。
根源码、原终局、工具链与线上仓库不变；最近额度剩余 55%，继续工作。

## 第十七轮续：内部编号递归的对象方案

新增初段相同、阶段稳定、唯一递归解及对象方案四模块。严格初段局部性与
全域性写在方案的前提中；不假定外部良基性，不添加递归或真谓词公理。

串行验收：桥接 1701 jobs；原终局公理检查通过；有限层 63、独立二阶 2541、
全桥接 5174 个声明通过，仅三项标准公理。450 条旧警告逐条相同、新模块零；
两树 125 个改动或新增 Lean 文件哈希相同，差异检查通过。

日志：`outputs/bms-z2-ranked-recursion-bridge.log`、`bms-z2-ranked-recursion-audits.log`。
随后逐点规则适配模块不计入本检查点。根源码、原终局、工具链与线上仓库
不变；最近额度剩余 54%，继续实现具体求值规则，未宣称 BM4 的降阶完成。

## 第十八轮首段：实际求值规则与唯一内部解

新增逐点规则适配、具体求值规则、求值固定点三模块，扩充前插公式的任意
项实例及原始语义。完整参数闭句给出唯一内部求值解，不留下局部性假设。

串行验收：桥接 1704 jobs；原终局公理检查通过；有限层 63、独立二阶 2631、
全桥接 5264 个声明通过，仅三项标准公理。450 条旧警告逐条相同、新模块零；
两树 128 个改动或新增 Lean 文件哈希相同，差异检查通过。

日志：`outputs/bms-z2-evaluation-fixed-point-bridge.log`、`bms-z2-evaluation-fixed-point-audits.log`。
后续赋值换码和构造子方程不计入本检查点。根源码、原终局、工具链与线上
仓库不变；额度最近剩余 53%，继续工作，未宣称源语法对应或 BM4 降阶完成。

## 第十八轮续：赋值换码不变性与构造子方程

新增赋值读取相同、求值换码、构造子方程三模块。使用内部反例集合最小元
覆盖所有模型公式编号，存在量词真值不依赖正确前插数码的选择。

串行验收：桥接 1707 jobs；原终局公理检查通过；有限层 63、独立二阶 2687、
全桥接 5320 个声明通过，仅三项标准公理。450 条旧警告逐条相同、新模块零；
两树 131 个改动或新增 Lean 文件哈希相同，差异检查通过。

日志：`outputs/bms-z2-evaluation-equations-bridge.log`、`bms-z2-evaluation-equations-audits.log`。
根源码、原终局、工具链与线上仓库不变，未提交或推送。源语法正确性、`Def`、
`L*` 及固定高度 BM4 的 PRA `(G)` 仍待完成；额度最近剩余 53%。

## 第十九轮首段：上游源语法的完整求值正确性

新增源公式编译、环境表示、派生逻辑方程和源满足关系四模块。所有上游纯
集合公式均有编译正确性；源结构的数域呈现条件保持显式，未偷换 BM4 编码。

串行验收：桥接 1711 jobs；原终局公理检查通过；有限层 63、独立二阶 2724、
全桥接 5357 个声明通过，仅三项标准公理。450 条旧警告逐条相同、新模块零；
两树 135 个改动或新增 Lean 文件哈希相同，差异检查通过。

日志：`outputs/bms-z2-source-satisfaction-bridge.log`、`bms-z2-source-satisfaction-audits.log`。
后续环境赋值存在性及统一子集族不计入本检查点。根源码、原终局、工具链与
线上仓库不变，未提交或推送；最近额度剩余 52%，继续工作。

## 第十九轮续：赋值存在性与统一定义子集族

新增源赋值存在、内部子集族、源公式覆盖和族对象定理四模块。全族由一次
实际理解构造，原环境表示前提的存在性已补齐；尚未等同于集合论 `Def`。

串行验收：桥接 1715 jobs；原终局公理检查通过；有限层 63、独立二阶 2755、
全桥接 5388 个声明通过，仅三项标准公理。450 条旧警告逐条相同、新模块零；
两树 139 个改动或新增 Lean 文件哈希相同，差异检查通过。

日志：`outputs/bms-z2-definable-family-bridge.log`、`bms-z2-definable-family-audits.log`。
后续代表关系和切片相容性不计入本检查点。根源码、原终局、工具链与线上
仓库不变；最近额度剩余 52%，继续工作。

## 第二十轮首段：内部全部切片的代表不变性

新增相关赋值、求值代表不变性和切片相容性三模块。明确要求 Q 在全数域
自反，且 Q、R 对 Q 对应相容；并未把仅在 D 上的较弱条件静默替代进去。

串行验收：桥接 1718 jobs；原终局公理检查通过；有限层 63、独立二阶 2787、
全桥接 5420 个声明通过，仅三项标准公理。450 条旧警告逐条相同、新模块零；
两树 142 个改动或新增 Lean 文件哈希相同。后续统一子集图层不计入本检查点。

日志：`outputs/bms-z2-definable-respect-bridge.log`、`bms-z2-definable-respect-audits.log`。
根源码、原终局、工具链与线上仓库不变；最近额度剩余 51%，继续进行小范围
图商集合对象构造，到剩余 50% 时整理停工。

## 第二十轮续：统一子集族的实际集合代码

新增统一子集图层及其集合收集两模块。整个内部选择关系由一张图承载，
再以单根拼接形成实际集合代码；其完整成员规格不使用外部族收集假设。

串行验收：桥接 1720 jobs；原终局公理检查通过；有限层 63、独立二阶 2811、
全桥接 5444 个声明通过，仅三项标准公理。450 条旧警告逐条相同、新模块零；
两树 144 个改动或新增 Lean 文件哈希相同，差异检查通过。

日志：`outputs/bms-z2-subset-collection-bridge.log`、`bms-z2-subset-collection-audits.log`。
后续成员正规化和结构呈现不计入本检查点。根源码、原终局、工具链与线上
仓库不变；额度最近剩余 51%。

## 第二十一轮首段：实际成员结构及定义子集收集上界

新增成员正规化、实际原子图、成员结构及可定义子集对象四模块。实际图商
成员结构的数域呈现条件已构造，不再留给调用者。一个内部集合代码收集
全部上游源公式的参数定义子集，但尚未证明精确等于原语法中的 `Def(A)`。

串行验收：桥接 1724 jobs；原终局公理检查通过；有限层 63、独立二阶 2841、
全桥接 5474 个声明通过，仅三项标准公理。450 条旧警告逐条相同、新模块零；
两树 148 个改动或新增 Lean 文件哈希相同，差异检查通过。

日志：`outputs/bms-z2-definable-objects-bridge.log`、`bms-z2-definable-objects-audits.log`。
后续全内部相容成员族和精确切片读取不计入本检查点。根源码、原终局、
工具链与线上仓库不变；最近额度剩余 51%，未提交或推送。

## 第二十一轮收尾：统一相容成员族、精确切片读取与额度停工

将上一段已逐模块编译的 `SecondOrderMemberFamily` 和
`SecondOrderSubsetExact` 接入桥工程、独立二阶导入白名单、必需声明检查
及显式公理打印。本阶段没有展开新的证明定理。

2026-09-13 串行验收：桥接构建成功，1726 jobs；原终局公理检查通过；
有限层 63、独立二阶 2843、全桥接 5476 个声明通过公理审计，依赖只允许
`propext`、`Classical.choice`、`Quot.sound`。450 条历史警告与
`bms-z2-domain-bridge.log` 逐条相同，新增警告为零。主树与短验证树的
150 个改动或新增 Lean 文件哈希全部相同；差异检查通过。二阶源码的
占位证明、额外公理及禁止捷径扫描无命中。

日志：`outputs/bms-z2-member-family-bridge.log`、
`outputs/bms-z2-member-family-audits.log`（均在仓库同级 `outputs/`）。
这是本地增量构建与审计，不是冷缓存验证，也不是远端 CI；本收尾未重跑
根工程。原终局、工具链及线上仓库未修改，未提交或推送。

收尾前后实时额度均显示普通额度已用 50%、剩余 50%。按用户要求整理后
停止，无遗留 Lean／Lake 构建进程。数学断点和恢复顺序已写入
`SECOND_ORDER_HANDOFF.md`。精确 `Def(A)`、可构造递归、正确 L* 的收集和
反射、固定高度 BM4 对象证明及 PRA `(G)` 仍未完成；不宣称达到 Z₂ 或
候选的略强反射背景。

## 第二十二轮首段：恢复工作并完成相容成员族集合装配

用户在 2026-09-13 明确解除剩余 50% 停工限制，并要求完成后保留旧
ZFC／可构造证明版本和弱背景版本。新增 `SecondOrderMemberCollection`
的统一集合装配与精确源参数定义覆盖定理已完成，不改变原 BM4 目标。

检查点 `member-collection`：桥构建 1727 jobs；原终局公理检查通过；
有限层 63、独立二阶 2845、全桥接 5478 个声明通过，仅三项标准公理。
450 条历史警告逐条相同、零新增。新增三阶候选理论不计入该检查点。

日志：仓库同级 `outputs/bms-z2-member-collection-bridge.log`、
`outputs/bms-z2-member-collection-audits.log`。旧线上仓库与工具链未变，
未提交或推送。后续新背景的公理定义和语义核验必须通过单独审计，不能
混称为已经完成 BM4 的三阶降背景证明。

## 第二十二轮三阶背景检查点：明确公理与内部 Cantor

检查点 `third-order-bounds`：桥构建 1762 jobs；原终局公理检查通过；
有限层 63、独立二阶 2845、全桥接 5607、独立三阶 129 个声明通过，
只允许三项标准公理。450 条历史警告逐条相同、零新增。157 个改动或
新增 Lean 文件与短验证树哈希相同；163 个旧资源的内容快照检查通过；
差异检查通过。此后增添的幂集传回模块不计入这一检查点。

新增接口已从精确公理提取共同的 ω、P(ω)、所有集合到该共同实数对象
的单射及内部集合良序；内部 Cantor 对角子集由实际分离构造。独立三阶
检查禁止旧可构造宇宙、宿主 Ordinal 及原最终组装模块导入。

早先 `third-order-core` 检查曾发现上游 notation 生成的原生闭合证书
进入新理论定义的依赖。现已改为结构性闭合证明及已有反向语法桥，
没有放宽审计、删除上游资源或加入证明公理。保留失败日志供复核。

日志：仓库同级 `outputs/bms-third-order-bounds-bridge.log`、
`outputs/bms-third-order-bounds-audits.log`。这是本地增量检查，不是冷缓存
或远端 CI；未重跑根工程，也未提交或推送。内部模型、统一满足关系、
稳定对及 BM4 对象证明尚未完成，不能据此宣称完成降背景。

## 第二十二轮后续：无幂集构造、内部归纳与实际函数图

所有检查继续串行，LEAN_NUM_THREADS=1。各本地增量检查点为：

| 检查点 | 桥构建 jobs | 全桥声明 | 独立三阶声明 |
| --- | ---: | ---: | ---: |
| third-order-power | 1914 | 5662 | 184 |
| third-order-induction | 1915 | 5673 | 195 |
| third-order-order | 1917 | 5682 | 204 |
| third-order-mapping | 1918 | 5699 | 221 |
| third-order-functions | 1921 | 5708 | 230 |
| third-order-natural-order | 1923 | 5729 | 251 |
| third-order-coordinates | 1924 | 5741 | 263 |
| third-order-recursion | 1929 | 5796 | 318 |
| third-order-order-type | 1941 | 5851 | 373 |
| third-order-omega-one | 1944 | 5876 | 398 |
| third-order-selection | 1948 | 5903 | 425 |
| third-order-addition | 1955 | 5943 | 465 |
| third-order-addition-order | 1957 | 5951 | 473 |
| third-order-countable-bounds | 1969 | 6025 | 547 |
| third-order-well-recursion | 1978 | 6133 | 655 |
| third-order-finite-assignments | 1985 | 6203 | 725 |
| third-order-evaluation | 1993 | 6312 | 834 |
| third-order-evaluation-family | 2000 | 6372 | 894 |
| third-order-source-compilation | 2007 | 6414 | 936 |
| third-order-source-coverage | 2013 | 6447 | 969 |
| third-order-hierarchy | 2023 | 6500 | 1022 |
| third-order-hierarchy-limit | 2029 | 6528 | 1050 |
| third-order-witness-bound | 2037 | 6570 | 1092 |
| third-order-skolem-closure | 2043 | 6615 | 1137 |
| third-order-elementarity | 2051 | 6657 | 1179 |
| third-order-pair | 2053 | 6673 | 1195 |
| third-order-bounded | 2058 | 6709 | 1231 |
| third-order-certificate | 2061 | 6742 | 1264 |
| third-order-delta | 2066 | 6762 | 1284 |
| third-order-levy | 2073 | 6858 | 1380 |
| third-order-level-one | 2079 | 6885 | 1407 |
| third-order-polarity | 2084 | 6940 | 1462 |
| third-order-stage-stability | 2090 | 6974 | 1496 |
| third-order-stable-boundary | 2094 | 7008 | 1530 |
| third-order-source-complexity | 2099 | 7029 | 1551 |
| third-order-finite-source-reflection | 2104 | 7048 | 1570 |
| third-order-ordinal-height | 2109 | 7091 | 1614 |
| third-order-omega-absolute | 2111 | 7099 | 1622 |
| third-order-finite-graph-closure | 2115 | 7118 | 1641 |
| third-order-finite-addition-absolute | 2120 | 7153 | 1676 |
| third-order-triangular-stage | 2125 | 7192 | 1715 |
| third-order-original-source-absolute | 2131 | 7226 | 1749 |
| third-order-evaluation-absolute | 2137 | 7247 | 1770 |
| third-order-evaluation-source | 2143 | 7303 | 1826 |
| third-order-evaluation-range | 2150 | 7320 | 1843 |
| third-order-evaluation-member | 2158 | 7371 | 1894 |
| third-order-slice-family | 2167 | 7396 | 1919 |
| third-order-stage-core | 2174 | 7436 | 1959 |
| third-order-hierarchy-absolute | 2178 | 7450 | 1973 |
| third-order-certificate-absolute | 2187 | 7481 | 2004 |
| third-order-core-stage | 2194 | 7512 | 2035 |
| third-order-finite-core | 2202 | 7585 | 2108 |
| third-order-finite-operator | 2209 | 7672 | 2195 |
| third-order-finite-hierarchy | 2216 | 7722 | 2245 |
| third-order-finite-stability | 2219 | 7729 | 2252 |
| third-order-bounded-truth | 2223 | 7751 | 2274 |
| third-order-ambient-existential | 2228 | 7778 | 2301 |
| third-order-truth-record | 2234 | 7836 | 2359 |
| third-order-truth-certificate | 2239 | 7878 | 2401 |
| third-order-truth-monotone | 2241 | 7884 | 2407 |

每个检查点都同时通过原终局公理审计、有限层 63 和独立二阶 2845 个
声明的审计；只允许 propext、Classical.choice、Quot.sound。最新检查点
的 450 条历史警告与基线逐条相同，零新增；485 个改动或新增 Lean 文件
与短验证树哈希相同，163 个既有资源快照未变。差异与禁止捷径扫描通过。

最新检查点另通过 62 个指定正向出口的类型和证明正文常量依赖检查：
不引用 `ThirdOrderTheory.bound_m`、其公理构造子、`bound_l` 或
`ThirdOrderSemantics.bounds_l`。该检查不遍历未使用的归纳构造子，
不替代公理审计，也不宣称已经将所有完整理论参数消去或完成强度校准。
两个实际抽取接口为 `ThirdOrderOmegaOne.of_power_l` 和
`ThirdOrderSelection.of_choice_l`；本理论定义本身没有改变。

前一检查点六个新模块证明原加法迭代图在 Cω+2/proper 极限层的成员性，原无限
加法和原配数公式的绝对性，以及域内候选 S 的原有限赋值全集判定绝对性。
没有改写原加法/配数/assignments 模板，也不将整个赋值集合的成员性计为
已证。日志为工作区 outputs 下 `bms-third-order-original-source-absolute-bridge.log`
及 `bms-third-order-original-source-absolute-audits.log`。本次是本地增量桥
构建和相关完整审计；没有重跑根工程或远端 CI，也没有提交或推送。

检查点 `third-order-evaluation-absolute` 新增六个模块、21 个实际
导出的公开定理，覆盖原节点/构造子、赋值更新及原子查询、存在量词、
四分支局部求值、原分离求值步、序数前史和递归求值语义的绝对性。
实际 proper 极限层出口消去加法迭代、有限图闭包与局部等价前提；
统一值域由图的二次并取得，所有内部自然数前史由有限图闭包取回。
A、S、F 仍是域内参数，原 evaluation_m 额外关系图 R 的成员性未计为已证。

首次独立审计发现源码中的 `PowerlessValueAbsolute.update_source_l`
没有实际导出，虽然模块构建返回成功。将该接口提前到同名 member_l
声明之前并采用显式证明块后，独立导入核对六个声明全部存在，再重跑
完整构建与全部审计成功；未删除待审接口或放宽任何守卫。此次没有
隔离判定编译器根因，不将该现象笼统归因于缓存或工具链。

最终全门会话 60859 返回 exit 0：桥 2137 jobs、全桥 7247、独立三阶
1770、独立二阶 2845、有限层 63，原终局审计通过；只有三项标准公理。
完整构建结束后重核两树 381 个 Lean 文件、450 条旧警告、163 个冻结
资源、差异及禁止项，全部通过。第七个规模界无关出口为
`PowerlessEvaluationAbsolute.stage_l`，不将此检查当作对象强度定理。
日志为 `outputs/bms-third-order-evaluation-absolute-bridge.log` 和
`outputs/bms-third-order-evaluation-absolute-audits.log`（均位于仓库同级）。
本次仍未重跑根工程、未运行远端 CI、未提交或推送。

检查点 `third-order-evaluation-source` 新增六个模块、25 个公开
声明（4 个定义、21 个定理）；计入编译生成声明后，独立审计净增 56 个。
原自然数隶属关系 R 已有实际极限层成员性；原 relation/history/recursion
桥不要求小结构核心，域内 R 自动给出相关有序对闭包。原 evaluation_m
在实际 proper 极限层上、任意项环境中的正确解释已完成。另以源覆盖
证明 A∈Cα（ω∈α，α 为极限）的全部有限赋值集合 S∈Cα+1，不能改写
成 S∈Cα。整个求值图 F、一般无限层次及 BMS 终局仍未完成。

最终全门会话 46085 返回 exit 0：桥 2143 jobs、全桥 7303、独立三阶
1826、独立二阶 2845、有限层 63，原终局审计通过。全部依赖只允许
三项标准公理；9 个正向出口未引用全集规模界，新增检查出口为
`PowerlessEvaluationSourceAbsolute.stage_l` 和 `PowerlessStageAssignments.exists_l`。
完整构建后检查 387 个 Lean 文件两树一致、450 条旧警告逐条不变、
163 个冻结资源不变；差异及禁止项通过。没有额外小结构核心假设，
也不将上述规模界依赖检查当作背景强度校准。
日志位于仓库同级 `outputs/bms-third-order-evaluation-source-bridge.log`
及 `outputs/bms-third-order-evaluation-source-audits.log`。未重跑根工程
或远端 CI，未提交、未推送。

检查点 `third-order-evaluation-range` 新增七个模块、15 个公开定理，
计入编译辅助净增 17 个被审计声明。原 clause 的逐点定义不使用 Y 作
参数，实际 proper 极限出口给求值输出的后继层成员性；Cκ 的早级
共尾性给有限输入参数共同落级，从而取得 S 和 Y 的 Cκ 成员性。
内部纯公式归纳取得原 F 的全部值和有限前史属于 Cκ；精确值域的内部
可数性再给一个共同早级界，其中 A/S 和所有有限前史都是元素。
仍只证明 F⊆该层，未宣称整个 F 的成员性或 BMS 弱背景终局。

全门会话 95012 返回 exit 0：桥 2150 jobs、原终局审计通过，有限层 63、
二阶 2845、全桥 7320、三阶 1843 个声明通过，仅允许原三项标准公理。
新增三个规模界无关检查出口为 `PowerlessStageEvaluationStep.operator_l`、
`ThirdOrderStageEvaluationRange.exists_l`、`ThirdOrderStageEvaluationBounds.exists_l`，
累计 12 个；这不是一致性强度降低的证明。全构建结束后，394 个 Lean
文件两树哈希一致，450 条旧警告逐条相同，163 个冻结资源未变，差异与
禁止项检查通过。日志为仓库同级 `outputs/bms-third-order-evaluation-range-bridge.log`
及 `outputs/bms-third-order-evaluation-range-audits.log`。没有未编译草稿、
残留的本轮构建、根工程重跑、远端 CI 或发布操作。

检查点 `third-order-evaluation-member` 新增八个模块、22 个实际
导出的公开声明（4 定义、18 定理），含编译辅助净增 51 个被审计声明。
保持原递归及步骤正文，以有限前缀证书定义整图成员条件，参数不含 F。
有限图闭包实际取得证书，源覆盖给 F∈D(Cβ)，再传入 Cκ。对 A∈Cκ，
已实际构造赋值集合 S 和原求值图 F，证明 S/F∈Cκ；不能以 A=Cκ 代入。
未假定小结构核心，也未把逐点子集关系当作集合成员性。

串行全门会话 35267 完成桥构建 2158 jobs、原终局及五项审计调用：
有限层 63、二阶 2845、全桥 7371、三阶 1894 个声明通过，只允许
propext、Classical.choice、Quot.sound。新增无规模界依赖检查出口为
`PowerlessEvaluationPrefixAbsolute.stage_l` 和
`ThirdOrderStageEvaluationMember.exists_l`，累计 14 个；不等于背景
强度已经降低。构建结束后，402 个 Lean 文件两树哈希一致，450 条旧
警告逐条相同，163 个冻结资源未变，差异及禁止项通过。
日志为仓库同级 `outputs/bms-third-order-evaluation-member-bridge.log`
及 `outputs/bms-third-order-evaluation-member-audits.log`。没有本轮残留
构建或待编译 Lean 草稿；未重跑根工程、远端 CI，未提交、未推送。
原 family/operator、一般无限层次/system、BM4 终局与强度校准仍待完成。

检查点 `third-order-slice-family` 新增九个模块、20 个公开定理，
全部实际导出，含编译辅助净增 25 个审计声明。原追加图、point/slice、
family 公式解释与切片/族的 Cκ 成员性已闭合；对 A∈Cκ 给出实际
D(A)∈Cκ，并完成原 operator_m 的任意项环境出口。原公式与参数槽
保持不变，不假定小结构核心，不把 A=Cκ 代入成员域前提。

串行全门会话 66288 返回 exit 0：桥 2167 jobs、原终局审计通过，
有限层 63／二阶 2845／全桥 7396／三阶 1919 个声明通过，仅三项标准
公理。新增规模界依赖检查出口为 PowerlessStageEvaluationSlice.operator_l、
ThirdOrderStageEvaluationFamily.member_l、ThirdOrderStageEvaluationOperator
的 exists_l 和 source_l，累计 18 个；此检查不是背景强度定理。
411 个 Lean 文件主/短树哈希一致，450 条旧警告逐条相同，163 个旧资源
未变；差异、禁止项通过，当前 Lake/Lean 进程数为 0。日志为仓库同级
`outputs/bms-third-order-slice-family-bridge.log` 及对应 `-audits.log`。

### Cκ 的完整核心及任意域内前史

检查点 `third-order-stage-core` 新增七个模块、23 个公开声明
（1 定义、22 定理），含编译辅助净增 40 个。已证明有限参数环境的
共同初等早级、Cκ 中完整源分离/收集、基础公理及原 Project 模式
回接，最终得到实际 `ThirdOrderStageCore.models_l`，没有内部 Core
假设。其直接应用为任意 f/a∈Cκ 的严格前史及任意 A∈Cκ 的原隶属
关系图的存在、成员性与所需原公式解释。递归公式桥只到小结构内
语义，尚未证明任意正文跨结构绝对，也未闭合层次/system 或 BM4。

串行全门会话 59470 返回 exit 0：桥 2174 jobs、原终局审计通过，
有限层 63／二阶 2845／全桥 7436／三阶 1959 个声明通过，仅允许
propext、Classical.choice、Quot.sound。全部新声明实际导出并审计；
25 个指定正向出口无规模界常量依赖。418 个 Lean 文件主/短树哈希
一致，450 条旧警告逐条相同，163 个冻结资源未变，差异与禁止项
检查通过。日志为仓库同级 `outputs/bms-third-order-stage-core-bridge.log`
及对应 `-audits.log`；未重跑根工程或远端 CI，未提交、未推送。

### 原无限层次、单层及求值系统

检查点 `third-order-hierarchy-absolute` 新增四个模块、14 个
公开定理，实际导出并审计，净增 14 个声明。实际 Core(Cκ) 已用于
原算子/累计步骤、整个层次图、单层和系统的内外语义一致。域内
序数上的原层次图 f∈Cκ，以及 α∈κ 的 A/S/F 系统成员性、存在性
均已证明；原 hierarchy_m、stage_m、system_m 保留正文及参数槽。
该检查点尚未接入原 stable_m；有限分类证书及查询一致见下一检查点。

串行全门会话 61495 返回 exit 0：桥 2178 jobs、原终局审计通过，
有限层 63／二阶 2845／全桥 7450／三阶 1973 个声明通过，仅允许
propext、Classical.choice、Quot.sound。31 个正向出口无规模界常量
依赖，422 个 Lean 文件主/短树哈希一致，450 条旧警告及 163 个
冻结资源未变，差异与禁止项检查通过，无遗留 Lake/Lean 进程。
日志为仓库同级 `outputs/bms-third-order-hierarchy-absolute-bridge.log`
及对应 `-audits.log`；未重跑根工程或远端 CI，未提交、未推送。
该检查点没有完成 BM4 终局与精确强度校准。

### 原有限证书、查询一致与稳定公式

检查点 `third-order-certificate-absolute` 新增九个模块、30 个公开
定理，含编译辅助声明净增 31 个审计声明。有限子集成员性由内部 ω
归纳证明；有界证书、原 Lévy 记录及全部分类规则、完整分类证书均
双向对应。全部环境有限赋值上的查询一致及分层一致关系接回后，
`ThirdOrderStageStability.source_l` 实际解释原 stable_m，不修改正文
或参数槽。六个系统见证通过已证成员性取回，不增设内部 Core 假设。

串行全门会话 59700 返回 exit 0：桥 2187 jobs、原终局审计通过，
有限层 63／二阶 2845／全桥 7481／三阶 2004 个声明通过，仅三项
标准公理。34 个指定出口无规模界常量依赖；431 个 Lean 文件两树
哈希一致，450 条旧警告逐条不变，163 个冻结资源未变，差异与禁止项
检查通过。确认无遗留 Lake/Lean 进程。日志为仓库同级
`outputs/bms-third-order-certificate-absolute-bridge.log` 及对应
`-audits.log`。未重跑根工程或远端 CI，未提交、未推送。

绝对性出口的域为实际 Cκ，不能据此宣称所有 proper 极限早层满足
同样结论。早层的必要解释条件、BM4 重编号／反射合同、任意环境
下降实数的实际检查器、对象终局与标准类型化解释及强度校准仍待完成。

### 显式核心早层的通用绝对性

历史检查点 `third-order-core-stage` 新增七个 `PowerlessCoreStage*`
模块、31 个公开定理；实际 proper 极限层另外满足内部核心时，完整
赋值集、求值图、切片、原算子、前史、层次图及系统的闭包／内外
一致已证明，并接回未修改的原 stable_m。该内部核心前提没有消去，
不宣称所有 proper 早层满足它。五个 Cκ 专用模块复用通用结论，
以已证 Core(Cκ) 实例化；19 个旧接口类型指纹逐项不变。

串行全门会话 7275 返回 exit 0：桥构建 2194 jobs、原终局审计通过，
有限层 63／二阶 2845／全桥 7512／三阶 2035 个声明通过，仅三项
标准公理。36 个指定出口无规模界常量依赖，438 个 Lean 文件两树
哈希一致，450 条旧警告及 163 个冻结资源未变。差异、禁止项检查
通过，确认无遗留 Lake/Lean 进程。证据为仓库同级
`outputs/bms-third-order-core-stage-bridge.log` 和 `-audits.log`，
以及 `outputs/bms-core-stage-interface-before.log`／`-after.log`。
根工程和远端 CI 未重跑，未提交或推送。该检查点时有限核心支持、
BM4 反射、任意环境下降实数及对象终局、标准解释和精确强度仍未完成；
有限核心支持的后续实际结果见下节。

### 有限核心支持及原算子早层闭包

`third-order-finite-core` 全门会话 82341 exit 0：桥 2202 jobs、
全桥 7585／三阶 2108；八个新模块，45 个公开声明（29 个定理）。
原 Formula 相对化、原签名强完备性到实际 Hilbert 有限支持、
早层完整赋值集及求值图闭包均已实现。446 个 Lean 文件哈希一致，
39 个指定出口无规模界依赖，450 条旧警告和 163 个冻结资源未变。
证据为 `outputs/bms-third-order-finite-core-bridge.log` 及 `-audits.log`。

`third-order-finite-operator` 全门会话 29889 exit 0：
桥 2209 jobs，原终局通过；有限层 63／二阶 2845／全桥 7672／
三阶 2195 个声明通过，仅三项标准公理。七个新模块，59 个公开
声明（36 个定理）；含生成辅助声明净增 87，不混同这三项计数。
43 个无规模界出口，453 个 Lean 文件哈希一致，450 条旧警告
和 163 个冻结资源未变；差异、禁止项检查通过，无遗留 Lake/Lean。
证据为 `outputs/bms-third-order-finite-operator-bridge.log` 及 `-audits.log`。

四个新有限支持覆盖原切片、任意前史、隶属关系图和完整算子存在。
`PowerlessFiniteStageClosure` 由有限理论和实际绝对性取得域内
见证；`PowerlessFiniteStageOperator.source_l` 保留原源两个存在
量词，不假定内部完整核心。`ThirdOrderFiniteStageOperator`
从 Core(Cκ) 反射合成的有限片段，给先于早层端点选定的同一个预算，
继而证明对所有 B∈Cα，原算子输出 D(B)∈Cα。
这不涵盖任意 proper 早层，也不完成原层次/system/stable 的全部
有限片段解释、BM4 终局或精确背景强度。
两次检查均未重跑根工程或远端 CI，未提交或推送。

### 原层次及完整系统的有限片段解释

`third-order-finite-hierarchy` 全门会话 59924 exit 0：桥 2216
jobs，原终局通过；有限层 63／二阶 2845／全桥 7722／三阶 2245 个
声明通过，仅三项标准公理。七个新模块、28 个公开声明（21 个定理），
含生成辅助声明的审计净增 50。47 个指定出口无规模界依赖，460 个
Lean 文件哈希一致，450 条历史警告逐条不变、163 个冻结资源未变；
差异和禁止项检查通过。无遗留 Lake/Lean，未重跑根工程或远端 CI，
未提交或推送。证据为 `outputs/bms-third-order-finite-hierarchy-bridge.log`
及 `-audits.log`。

原 step/rule/recursion/hierarchy/stage/system 的源解释均保留原
公式及实际量词，不假定早层满足完整核心。原层次存在闭句已有实际
Hilbert 有限支持；环境唯一性识别完整递归图，适用于任意内部序数。
同一个预先选定的反射预算给原稳定早层的合成有限理论，并使其下方
各层的完整层值、赋值集及求值图都属于该早层。

这不完成原 stable_m 的有限片段源解释、BM4 重编号及完整反射合同、
任意环境下降实数检查器或对象终局。非计算有限支持不等于可执行的
证明生成器；无规模界依赖不等于删除 P(ω) 存在，也不是 Z₂／Z₃
一致性强度比较。标准类型化解释、精确强度和最终双版本仍待完成。

### 原稳定公式的有限片段解释

`third-order-finite-stability` 全门会话 95625 exit 0：桥 2219
jobs、原终局通过；有限层 63／二阶 2845／全桥 7729／三阶 2252
个声明通过，仅三项标准公理。三个新模块，四个公开定理，含生成
辅助声明净增 7。49 个指定出口无规模界依赖，463 个 Lean 文件
哈希一致，450 条历史警告逐条不变，163 个冻结资源未变；差异与
禁止项检查通过。无遗留 Lake/Lean，未重跑根或远端 CI，未提交
推送。证据为 `outputs/bms-third-order-finite-stability-bridge.log`
及 `-audits.log`。

原极限／proper 公式只需环境核心和子域传递性。原 stable_m 保留
六个系统见证与查询方向，反向由实际有限系统成员性取回见证，
不调用需小层核心的旧稳定源表示。三阶出口先选统一预算，再
量化所有原环境和内部层号；有限模型性和实际参数均由已有构造
取得。尚需 BM4 复杂度重编号、完整有限反射（含上端点稳定边）、
任意下降实数与对象终局、标准解释和精确强度，本轮未改变背景公理。

### 不含全局真值参数的证书可靠性

限时增量 `third-order-truth-monotone` 全门会话 25276 exit 0：
桥 2241 jobs；原终局、有限 63／二阶 2845／全桥 7884／三阶
2407 个声明审计通过。两个模块的六个定理给出局部规则对
记录集的单调性，以及给定真实二元并集的 certificate_m 保持。
485 个 Lean 文件哈希一致、163 个旧资源不变、450 条旧警告
逐条相同、62 个无规模界出口及差异／禁止项通过。未重跑根
或远端 CI，未提交推送。证据为同级 outputs 中
`bms-third-order-truth-monotone-bridge.log` 和 `-audits.log`。
详见背景第 58 节；限时增量后停止，未完成任意族收集或完备性。

前一 `third-order-truth-certificate` 全门会话 61946 exit 0：桥 2239
jobs；原终局、有限层 63／二阶 2845／全桥 7878／三阶 2401 个
声明的审计通过，仅三项标准公理。五个新模块有 22 个公开声明
（11 个定理），含生成辅助声明净增 42；483 个 Lean 文件哈希
一致，450 条旧警告逐条不变，163 个冻结资源未变。差异、
禁止项及 60 个指定出口无规模界依赖检查通过。未重跑根或
远端 CI，未提交推送。证据为
`outputs/bms-third-order-truth-certificate-bridge.log` 及 `-audits.log`。

有界正／负分支保留真实有限函数图、无效更新槽与缺失界值
情形；有界识别与基例、与非、正存在、有界分支已经合成同一
不含 U／δ／H 的原 Formula。certificate_m 检查每个集合成员，
sound_l 以原公式内部码归纳证明整表可靠，accepts_source_l
实际消去子记录可靠性条件。无需外部有限记录集或外部 Acc。
维护中保留原语法、公共接口、模型前提和旧版资源。

尚需检查条件的添入／并集闭包、子证书族的当前层内收集及
固定层完备性。求值有限片段不自动包含新 Collection 实例。
实际有限支撑、固定层预算、BM4 终局与精确强度仍待证明。
详见背景文档第 56 节。


### 有符号集合记录与局部规则

前一 `third-order-truth-record` 最终全门会话 53885 exit 0：
桥 2234 jobs、原终局通过；有限层 63／二阶 2845／全桥 7836／
三阶 2359 个声明通过，仅三项标准公理。六个新模块、38 个公开
声明（27 个定理），含生成辅助声明净增 58。56 个指定出口无
规模界依赖，478 个 Lean 文件哈希一致，450 条旧警告逐条不变，
163 个冻结资源未变；差异和禁止项通过。无遗留 Lake/Lean，
未重跑根或远端 CI，未提交推送。证据为
`outputs/bms-third-order-truth-record-bridge.log` 及 `-audits.log`。

实际记录为 ⟨p,⟨c,f⟩⟩，原 Formula 表示、坐标落级、唯一性和
子域绝对性通过；记录集添入及任意集合族合并在实际极限层内
完成。与非／存在记录规则只消费严格较小原公式码的子记录可靠性，
不假定全表已经可靠。valid_l/valid_m 是语义后置条件，不是
证书接受条件；尚未闭合真正的局部证书及可靠性／完备性。

有界量词的界可能无限，因此下一步采用允许集合多个分支、
依靠内部码下降的证书；集合分支的收集、有界假分支和低层提升、
固定层预算、BM4 终局与精确强度仍待证明。旧版资源未改。

### 当前域存在量词真值

前一 `third-order-ambient-existential` 全门会话 78248 exit 0：
桥 2228 jobs、原终局通过；有限层 63／二阶 2845／全桥 7778／
三阶 2301 个声明通过，仅三项标准公理。五个新模块、18 个公开
声明（12 个定理），含生成辅助声明净增 27。53 个指定出口无
规模界依赖，472 个 Lean 文件哈希一致，450 条旧警告逐条不变，
163 个冻结资源未变；差异和禁止项通过。无遗留 Lake/Lean，
未重跑根或远端 CI，未提交推送。证据为
`outputs/bms-third-order-ambient-existential-bridge.log` 及 `-audits.log`。

实际函数图更新的定义域保持、域内有限赋值和合法槽位公式及其
当前层解释均已验证。量词规则同时取见证和真实更新图，已把原
有界真值公式实际填入正文，并与原存在构造子完整查询对应。
三阶实例消去正文解释假设，不预设赋值或槽位合法；U／δ／H
不是源公式参数。尚未覆盖全体正层内部证书的递归闭包、固定层
后继预算或 BM4 完整有限反射；对象终局和精确强度仍待证明。

### 当前域有界真值基例

前一 `third-order-bounded-truth` 全门会话 90870 exit 0：桥 2223
jobs、原终局通过；有限层 63／二阶 2845／全桥 7751／三阶 2274
个声明通过，仅三项标准公理。四个新模块、11 个公开声明（7 个
定理），含生成辅助声明净增 22。51 个指定出口无规模界依赖，
467 个 Lean 文件哈希一致，450 条旧警告逐条不变，163 个冻结
资源未变；差异、禁止项通过。无遗留 Lake/Lean，未重跑根或远端
CI，未提交推送。证据为 `outputs/bms-third-order-bounded-truth-bridge.log`
及 `-audits.log`。

原 truth_m 量化传递小域及其实际求值器，不以当前域或其完整
求值图作参数。任意合法内部有限赋值先放入实际早传递层，再由
求值有限片段取得完整见证，原有界证书正确性比较同码同赋值。
零层实例已接入 Cκ，覆盖原内部证书及两种合法极性。未将 truth_m
自身归为 Δ₀，未得到正层或全真谓词，未完成 BM4 完整反射、
任意下降实数及对象终局、标准解释、强度校准或双版本发布。


新增实际证明包括：收集加分离的精确函数像；当前纯公式的参数槽语义；
基础集合、有序对坐标唯一性、笛卡尔积；沿内部单射传回已有幂集；内部
自然数与良序的公式归纳；纯公式总唯一关系的实际函数图和精确值域。
后续函数接口已验证值的唯一性、图外延、精确限制、相容覆盖族之并；
相容并接口本身并不证明局部解存在。本轮随后由实际有限轨迹纯公式的
内部归纳证明了所有内部长度的轨迹存在、唯一及跨长度一致性，再收集
这些轨迹，完成 `PowerlessOmegaRecursion` 的实际总递归图及唯一性。
`PowerlessRecursionSyntax` 已核验该结论的原纯语言公式表示。
内部初段的后继边界、零／后继分解、可比性，以及关系坐标界和精确定义域、
值域也已完成；相容并现在可以处理各局部函数值域不同的情况。
三阶 Cantor 接口还排除了 P(P(ω))，不把完整幂集重新加入背景。

随后完成了实际内部良序坍缩函数、到上游内部序数的双射和关系对应。
由 P(ω) 的良序及其序型，分离出唯一首个不可数序数 κ，并核验该性质的
纯公式表示。这里没有使用宿主 `Ordinal`，也没有声称 κ 正则性已完成。

后续检查点完成了任意固定纯公式总关系的实际集合选择函数；为一族可数
集合统一选出到 ω 的单射；将其并集单射到“该族 × ω”。当时尚未完成可数
乘积可数，因此该检查点不包含可数并或取界结论。内部 ω 的序数接口
也已接通。加法检查点完成后继迭代、自然数值域、存在唯一性、纯公式表示、
左右零律、结合律、左右后继方程和交换律。`addition-order` 检查点再
核验精确保持后继的内部 ω 函数严格递增且单射，及加法严格单调、消去律。

`countable-bounds` 检查点再新增 12 个模块、74 个被审计声明，完成：
内部三角数状态的总算子和坐标归纳、实际三角数图、传递值域上的一般
严格增长引理、配对区间与坐标唯一性、ω×ω 到 ω 的实际单射；逐坐标
乘积映射；内部可数积、可数并、可数像与后继；κ 后继封闭、可数域
上的 κ 值函数严格有界以及无可数共尾函数。`ThirdOrderCountableBounds`
只消费实际内部函数图，没有把非标准内部 ω 当成宿主 Nat。

新证明图的独立审计继续禁止旧可构造语义和宿主 Ordinal 导入。旧终局
审计与 163 个原资源哈希再次通过；此前工作树改动保留，不恢复到旧提交。

`well-recursion` 检查点新增 9 个模块、108 个被审计声明：实际前驱图、
纯局部解公式、初段相容性、覆盖并、端点扩张，以及内部良序递归的存在
唯一性和纯表示。内部序数的 ∈ 图已从乘积分离，前驱域已精确识别；
`PowerlessOrdinalRecursion.exists_unique_l` 消去辅助关系图，直接得到
上游模型内部序数上的前史递归。其一步算子仍需证明总唯一，不把算子
性质或外部 WellFounded 当成新增公理。全部新源码单模块和全桥均已编译。

`finite-assignments` 检查点新增 7 个模块、70 个被审计声明：实际图末尾
扩张及反向分解、全部 n→A 图的精确层族、模型全部内部有限赋值的集合；
A 可数时该集合可数；保持域与值域的单坐标替换及唯一性；三角配数坐标界、
节点码的存在唯一与单射、子码严格递减。新模块未引入 P(A) 或宿主有限
序列假设。该检查点的全部有限赋值尚不包含统一求值器；后者由下轮实现。

`evaluation` 检查点新增 8 个模块、109 个被审计声明：实际二元载荷及
0、1、2、3 标签；读取有限图的隶属、等号、与非及索引存在量词纯局部
规则；分离真值子集的总唯一算子；内部序数递归实例化后的唯一实际求值
图；历史查询一致性、全内部不动点方程及四类构造子的精确方程；任意 A
上的实际编码/赋值/求值系统存在性，以及求值图的原纯语言表示。
源公式编译正确性、完整语法覆盖与精确 Def 仍未证明，未扩大成果口径。

`evaluation-family` 检查点新增 7 个模块、60 个被审计声明：有限参数图
末尾追加待定义元素后的实际求值切片、所有切片的精确集合像、可数域上
输出族可数；原子图坐标及单集合参数的成员语义对应；传递域包含于输出
且输出仍传递；空域输出精确为 {∅}；量化中间赋值集合和求值图后的
总唯一纯算子及结构性质。未引入 P(A)，未把原始求值族直接称为经典 Def。

`source-compilation` 检查点新增 7 个模块，并为已有节点补非零引理，共
新增 42 个被审计声明：不需数值满呈现的实际成员结构；源变量槽的范围、
新鲜性、图表示和更新保持；原子语义；由与非实现的全部命题联结词；
任意充分长赋值规格；两种源量词的实际更新对应；完整上游 Formula 的
内部数码存在及编译正确性。非空成员域和环境表示前提均保留。末尾 x
与量词预留槽的容量对齐、实际环境图存在、子集族参数覆盖仍未完成。

`source-coverage` 检查点新增 6 个模块，审计净增 33 个声明：固定末尾槽
的范围、新鲜性及压入保持；按完整上游 Formula 先构造独立容量界、再
覆盖所有足够大的末尾槽及环境；实际源环境自由/绑定上下文的有限图
实现；保留原值的实际填充图；同一数码和同一参数图对全部 x∈A 的源
切片对应，及其在实际输出族/总唯一算子上的覆盖。源更新与量词接口
只要求新槽不同于旧槽；原充分长编译接口保持，从统一容量定理推出。
上述上一检查点的表示及槽对齐缺口已补齐。不声称任意内部数码都能
反向解码为外部有限源公式，不声称经典 Def 等价或内部层次已实现。

`hierarchy` 检查点新增 10 个模块，并为已有源覆盖补 A∈D(A) 的空/非空
统一结论，审计净增 53 个声明。完成实际算子像映射及精确值域、任意前史
的累计并纯步骤及总唯一性、内部序数上的唯一层次函数及精确成员方程、
层次函数的纯表示；原 ∈ 关系的纯公式归纳及前史映射域；零值、嵌套、
前驱算子像包含、全部级传递、后继算子方程、极限并方程、早级属于后级；
可数前史域的一步保可数及任意图域内所有可数指标的层次值可数。
所有构造仅使用显式对象理论条件及实际集合函数，不使用宿主序数递归。
不同图域前缀相容、单级/Cκ 装配和所需经典 L 对应仍未证明。

`hierarchy-limit` 检查点新增 6 个模块、28 个被审计声明：序数初段的
真实函数限制保持完整前史，跨图域的前缀相容；单级纯定义、存在/唯一、
纯公式及任意较长图读值的等价；统一单级上的零/传递/包含/后继/极限/
成员及可数性；实际 Cκ 的非空、传递、全部早级可数并属于 Cκ、精确
早级并成员条件，以及同一域上的全部有限赋值和求值图；每个内部可数
B⊆Cκ 的真实级数选择函数、共同严格指标界及包含 B 的可数早级。
上述上一检查点的相容及 Cκ 装配缺口已补齐。实际 Skolem 见证闭包、
迭代极限封闭、反射及所需经典 L 对应仍未完成。

`witness-bound` 检查点新增 8 个模块、42 个被审计声明：原存在规则的
选定见证及真实更新图、实际三坐标请求的总化选择关系和纯公式、请求
集合上的真实选择图；覆盖全部内部自然数编码与内部有限赋值的可数
见证像；两域见证闭包条件的纯表示及缩小参数域/扩大见证域保持；每个
早级的严格更后可数见证界；两级严格步骤的纯公式与单级唯一性传递；
整个 κ 上的真实推进函数 H:κ→κ，以及它和实际 Cκ 求值系统的装配。
独立三阶审计增加全部 8 个模块及关键定理存在性检查；相关纯公式、
像集、取界及装配定理均实际执行了公理检查。新证明没有预设 κ 可数、
没有把宿主选择函数伪装成内部集合函数，也没有预设迭代闭包。

该检查点完成统一单步推进，不包含 H 的实际 ω 迭代、共尾上确界、
极限以下内部有限参数的统一落级或极限见证闭包。下一步须逐项实现，
不能用已证明的 Cκ 共同早级界跳过这些义务。

`skolem-closure` 检查点新增 6 个模块，并为自然数界补严格版本，净增
45 个被审计声明：真实自映射的纯总化步骤、内部迭代实际图和保持值域
的内部归纳及纯表示；真实见证推进序列及全内部严格单调性；实际值域
之并的纯公式、存在唯一、序数性、最小上界和有界并仍低于 κ；严格序列
每项属于该并、初值严格低于精确共尾极限、极限可数级的精确序列并式；
任意内部有限赋值全部参数统一落入序列某一级的纯公式及内部归纳；
极限级本身的真实存在见证闭包，及它与实际 Cκ 求值系统的共同装配。
新增层次已核验可数、非空、传递和包含于 Cκ；不是只核验逐点见证界。

上述上一检查点的实际迭代、精确极限、内部有限参数统一落级和极限
见证闭包义务均已完成。本检查点仍不包含内部求值器间语义一致性、
源初等性/反射、proper 稳定对、最终对象 BM4 良序性或背景强度校准。

`elementarity` 检查点新增 8 个模块，并补更新图实际值域收缩，净增
42 个被审计声明：真实见证闭包下的存在规则和局部规则比较；全内部
数码求值一致性质的纯公式及内部序数归纳，实际子域求值器的构造；
任意起点以上一致早级与 Cκ 求值系统的装配；同一码/小域有限参数的
求值子集精确限制及其在小域实际求值族中的成员性；原成员结构的环境
包含、压入保持、项值/原子/图表示对应；单一 U 求值器编译的源见证
准则；原 Formula 所有构造子的带参数初等性；最终将两项语义结论
装配到同一个实际 Cξ。内部全码归纳没有改成宿主 AST 归纳，源语义
证明也没有从两次独立编译存在性推出数码相同。两个结论均各自验证。

上述上一检查点的求值器语义一致与源初等性义务已经完成。

`pair` 检查点新增 2 个模块，并加强非冻结的新路线闭包/反射接口以保留
精确极限层号，净增 16 个被审计声明。实际恒等单射与序数比较证明 ω∈κ；
原纯公式表达非零极限及 ω<ξ<β；源环境包含复合与两条分别证明的
`interpolate_l` 实际消去共同上域，内部一侧保持同一有限赋值图并提升
其值域。最终 `ThirdOrderElementaryPair.exists_l/system_l` 构造
α∈ξ∈β∈κ、ω∈ξ、两端极限、实际可数/非空/传递 Cξ⊆Cβ 及其全部有限
赋值集合/求值图，证明两域之间的原源初等性和全内部数码一致性。
`system_l` 同时实际构造所需 U/S/F，没有新加上层或求值器存在公理。

`bounded` 检查点新增 5 个模块，净增 36 个被审计声明。实际成员有界
量词的纯公式、更新前界值与更新后 guard 的对应、传递子域中的真实
见证/全更新图值域恢复均已证明。复合数码保持 i≠j，实际存在且唯一，
参数和子码严格小于整码，对任意现有求值器具有精确有界量词语义。
成员、等号、NAND、有界存在均具备同码局部绝对性规则，不借全初等性。
同时构造原上游 Lévy 嵌入全部字段并核验环境对应，复用原 IsDelta0
全构造子的绝对性；原有界存在编译接口保留指定复合码及新槽条件。

`certificate` 检查点新增 3 个模块，净增 33 个被审计声明。证书是有
内部自然数上界的实际码集合，逐项按零/原子/NAND/有界存在生成；
生成、证书和识别关系均给原纯公式。正确性先纯公式化，再沿内部 ω
归纳，消费严格子码界，对任意内部证书证明传递小域上的查询一致。
证书并和添点实际由共同自然数界中的分离构造，并由规则单调性保持
旧项；所有生成构造的识别闭包均已证明。未用宿主有限列表或外部 Acc。

`delta` 检查点新增 5 个模块，净增 20 个被审计声明。实际 NAND 构造
同时给码、证书和查询方程，全部布尔派生保持这些证据；原有界存在
消费指定复合码，全称经反例存在与否定编译，guarded 存在经原成员
guard 的语义证据证明有界。原 IsDelta0 全部 12 个构造器均已编译，
先容量界后任意保护槽/环境的顺序不变。实际参数图实现与长度填充
给同一码、同一证书、同一参数图对所有待定义元素的统一覆盖；实际
求值子集接口也保留编码、证书和指定切片来源。

`levy` 检查点新增 7 个模块，净增 96 个被审计声明。实际记录 (c,n,p)
及局部层级规则、证书与分类均有原纯公式。已构造实际有限记录集的
合并和扩充，验证同极性层号单调、严格升层到任意极性，并给同一
NAND/有界存在/无界存在构造子的分类闭包。纯公式内部码归纳证明零层
恰为已有有界类；普通 ∃i(假) 码第一层接受、零层拒绝的通用正负定理
也已通过。此区分只关乎语法分类，不是语义层级严格性或强度下界。
跨极性升层读取同码时必须严格降层，其余规则消费严格较小公式码。

`level-one` 检查点新增 6 个模块，净增 27 个被审计声明。原极性到内部
标签的对应、任意内部层号的布尔同码分类及语义、原源有界量词和正层
Σ 存在/Π 全称编译均已证明。原 IsLevel1 全部 9 个构造器的带证书
容量归纳已闭合，复用 Δ₀ 覆盖；同一码、分类和实际参数图对所有追加
元素统一有效，实际求值子集仍保留 c/g/B 与指定切片来源。无界存在
消费实际指定构造子，不从两次语义存在性推出同一码。

`polarity` 检查点新增 5 个模块，净增 55 个被审计声明。同一小域的
全部内部有限赋值上，Σ 向上／Π 向下方向已给原纯公式。实际无界
存在向上与有界存在的双向局部规则已接到求值器方程；向下恢复见证
和整个更新图的值域。真正量化 n 层证书的查询一致及全部 m∈n 的
低层一致都有原纯公式、下降单调、零层一致及第一层低层一致定理。
内部证书的极性正确性沿实际 ω 的数码作纯公式归纳，同码升层和
跨极性存在显式消费严格低层一致；一般定理保留这个前提。第一层
实例由已证零层绝对性消去该前提，不额外假定初等性，也不声称第一层
双向绝对。全部新增定理均经独立三阶导入／公理审计。

`stage-stability` 检查点新增 6 个模块，净增 34 个被审计声明。实际
层、全部有限赋值集合和求值图已合成具有存在/联合唯一性的原纯关系；
内部 n 层稳定严格保留 proper 端点及 n 层证书范围，并与任意指定的
真实系统读取等价。真实赋值值域提升给查询复合/插值，再证明实际
端点的层号下降、传递、插值及零层实例。n 层稳定通过内部后继成员
方程给 n+1 层证书的极性保持。原纯公式分离加内部正则性构造固定 β
下最小稳定下端点，并证唯一、最小和层号单调；这不是可变上端点的
全局边界。工作理论实际给任意早级以上同一对端点对所有内部 n 稳定，
并为每个内部 n 给某个 β<κ 的最小下端点。尚未做 BM4 复杂度重编号。

`stable-boundary` 检查点新增 4 个模块，净增 34 个被审计声明。κ 内
具有可变 n 层稳定后继的候选下端点已给原纯公式和实际分离集合，
内部正则性给最小边界 σ；存在、最小、唯一、序数/内部自然数条件
及层号单调均已证明。α∈σ、β∈κ 的任意 m 层稳定关系必有 m∈n，
β 可等于或高于 σ；同时得到边界内统一有限支撑和无全层稳定后继。
所有内部 n 的边界由已证实际稳定对给出，再经纯总唯一关系收集为
唯一集合函数 F:ω→κ，图值精确等价于边界，实际图值具有单调和截断
接口；由内部可数取界得到共同严格界 ρ∈κ。未用外部标准性、外部
Acc 或宿主选择函数代替内部集合图。仍未做 BM4 复杂度重编号。

`source-complexity` 检查点新增 5 个模块，净增 21 个被审计声明。
原 Formula 的编译能力先固定内部层号，再量化域、求值器、槽界和
参数；每个输出保留同一码的分类与语义，容量先于任意保护槽确定。
全部布尔规则、真正有界量词不升层及正层同极性无界量词保持均已证明。
原 Formula 的全部 11 个构造器给域/参数无关的有限双极性编译界；
一般量词的保守上界不替代有界规则，也不声称最小。实际参数覆盖
保留同一 c/g 对所有追加元素的语义及指定求值子集来源。

`finite-source-reflection` 检查点新增 5 个模块，净增 19 个被审计
声明。有限正层查询一致对指定 Σ 子码的实际存在节点给小域见证，
再将同一子码查询传回上域求值器；原源版本只编译上域一次。
固定公式的反射合同、预算单调和全部布尔/量词规则已证明。递归原
Formula 的全部构造器，统一子式反射预算和编译预算后取实际内部
后继，给域与参数无关的有限反射层号。最终接到原始 n 层稳定的
真实 Cα/Cβ 系统，非空域和包含均由层性质给出。没有把两域独立
编译的存在性误作数码相等，也未把层内源真值反射当作 C 定义绝对性。

`ordinal-height` 检查点新增 5 个模块。传递成员域到原模型的原 Lévy
嵌入、有界序数源公式与 Δ₀ 证书、原序数公式的等价和子域绝对性均已
核验。指定序数截面实际属于 D(A)，空域使用其精确算子方程。原纯公式
内部序数归纳给全部实际 Cα 的 Cα∩Ord=α；下界来自早级序数截面进入
输出，上界由子集来源及内部序数比较给出。继而验证所有内部自然数
属于 Cω、ω 不属于 Cω，以及 α>ω 时实际 ω 和四个编码标签属于 Cα。
未预设 C=L，也未把内部序数归纳替换成外部良基。

`omega-absolute` 检查点新增 2 个模块、8 个被审计声明。原空集、
子集、后继和归纳集合判定对传递成员域绝对。若域实际含 ω，内层
最小归纳对象与 ω 比较、外层 ω 与该对象比较，再由外部核心的
外延性识别同一对象；由此核验原 omega_m 的任意项/环境满足性。
实际高于 ω 的 C 层出口已用刚证明的参数落级和层传递性消去这些
额外前提。未要求子结构满足完整核心，也没有删去 ω∈A 的条件。

`finite-graph-closure` 检查点新增 4 个模块，净增 19 个被审计声明。
原源覆盖先将指定空集、配对、后继及并放入实际 D 输出，空域另行处理。
极限层的有限参数由连续性、内部序数比较及层包含放入共同早级，再由
层次方程取得集合闭包。有序对/添元/图追加闭包随后接到原纯公式内部
ω 归纳：每个实际 f:n→Cα 都属于 Cα，覆盖全部内部 n∈ω，含 Cω 特例。
全部有限图的集合只证明是层的子集，不是元素；没有用此替代三角数图
等无限图落级。新增模块无警告、占位证明或额外内核公理。

`finite-addition-absolute` 检查点新增 5 个模块，净增 35 个被审计声明。
原配对、有序对、取值和映射判定只用传递性获得子域绝对性。有限加法
定义要求实际 n+1 长自然数值轨迹；原无限图的限制与既有轨迹唯一性
证明其与原加法同值。原 Formula 表示和逐项满足性已核验。轨迹正文
绝对性与存在见证落级分别证明；有限图闭包由 Cω 向每个更高实际层
传输，故有限加法在 Cω+1 起正确解释，不要求目标层为极限。
没有将该同值等价误作原无限迭代公式的小层绝对性，亦未假定子域核心。

`triangular-stage` 检查点新增 5 个模块，净增 39 个被审计声明。
内部有限三角数轨迹通过原纯公式 ω 归纳与实际 T 比较，有限加法作为
后继方程。原 Formula 的轨迹/值表示、有限图闭包下的子域解释均已
核验，未把 T 的域内成员性加作前提。成员公式逐点定义 T，源覆盖将
T⊆A 升为 T∈D(A)。实际 Cω 的自然数有序对闭包给 T⊆Cω+1，随后
构造 Cω+2 的指标/层见证并证明 T 属于该层；内部序数比较及层次方程
将 T 传入所有高于 ω 的 proper 极限层；`parameters_l` 精确合并
ω、e、T、t₁、t₂、t₃ 六个实际集合参数的层成员性。
未宣称旧无限加法、原配数代码、求值或层次定义已经绝对。

上述 proper 初等对、有界局部规则、原源 Δ₀ 绝对性、内部有界证书的
正确性/生成闭包，以及该证书的完整原源编译与统一参数覆盖现已完成。
内部极性/有限层号分类、生成闭包/单调性及零层精确性也已完成。
原源 Σ₁/Π₁ 的同码编译与统一参数覆盖也已完成。
任意内部证书的条件性极性保持、第一层单向保持，以及真实分层查询
一致的纯公式与下降单调性也已完成。
实际层上的原始分层关系及其序性质、后继层极性保持、共用端点的
全内部有限层实例和固定上端点的最小稳定下端点也已完成。
κ 内可变稳定后继的有限层最小边界及截断、全内部有限层边界的唯一
集合函数图与共同严格上界也已完成。
一般固定源公式的统一有限编译界、指定正层见证准则、有限反射预算
及真实层上的带参数源真值保持也已完成。
全部 C 层的正确内部序数高度、实际 ω 和四个标签的落级、原序数
及归纳集合判定的传递子域绝对性、含 ω 层的原 ω 公式正确解释也已完成。
实际极限层的基本集合闭包、全部内部有限赋值图落级也已完成。
原函数图绝对性、有限加法的同值等价及每个高于 ω 层的有限加法
正确解释也已完成。
三角数有限轨迹/值/成员公式解释与整个实际 T 的早级成员性也已完成。
上述旧断点中，原加法及编码、赋值全集和层次／求值历史的所需落级，
以及 Cκ 中原层次／系统／稳定公式的绝对性，现已由后续检查点完成。
仍未完成 BM4 的具体重编号／反射合同及所需早层解释条件、所需 L
对应或当前 C 层次的等效证明性质、任意环境下降实数检查器、最终
对象 BM4 良序性和类型化三阶解释及强度校准。

本轮收尾没有自有后台构建、占位证明或未编译新增 Lean 文件。

日志分别为仓库同级 `outputs/bms-<检查点>-bridge.log` 与
`outputs/bms-<检查点>-audits.log`。新三阶审计已加入检查脚本和 CI 配置；
本轮未运行远端 CI、未重跑根工程、未提交或推送。上表仍不证明背景强度
校准、经典 L 对应、BM4 反射合同或 BM4 的
新对象主定理完成。
