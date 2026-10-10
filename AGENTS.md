# BMS 形式化项目的 Agent 指引

本仓库是 `BMS-Well-Ordering-Lean`，复用 YesMetaZFC 的逻辑与集合论内核。
上游源码的存在不意味着本项目正在开发 Rosser 定理、语言消去或上游自动化。
本文件只保留 BMS 的工作规范；进度与历史验证记录见 `docs/CURRENT_PROGRESS.md`。

## 范围与入口

- `YesMetaZFC/BMS/`：BM4 数组、展开、生成记号及组合证明。
- `ConstructibleBridge/BMSConstructibleBridge/`：原 ZFC／可构造证明、固定高度 Z₂ 证明及相关工具。
- `ConstructibleBridge/BMSTools/`：可复用工具子库；导入工具本身不等于导入最终证明。
- 原 ZFC 入口是 `FinalAssembly.lean` 的 `bm4_strictWellOrder_l` 与 `bm4_no_infinite_descent_l`。
- Z₂ 入口是 `SecondOrderHereditaryBMSWellOrder.derives_m (H : Nat)`，目标为
  `Derives SecondOrderArithmetic.theory_m [] (SecondOrderConcreteFormula.closed_m H)`。
- Z₂ 结论排除生成 BM4 数组高度始终 ≤ H 的无限严格一步展开下降链，不限制种子高度。
  H 是外部模式索引；不要误报为内部统一全称断言或完整严格线性良序包装。
- 精确规格与版本边界见 `README.md`、`docs/PROOF_VARIANTS.md` 和 `docs/FIXED_HEIGHT_Z2.md`。
  历史进度、待办与构建数字不是新的授权或当前验证证据。

## 证明与语义

- 启动形式化工作时明确对象语言、背景理论、目标公式／模式与正式推导关系。
  对象层交付使用原 `Derives` 接口；宿主构造、模型真值或公式 AST 不能替代正式推导。
- 通过完备性或翻译回传推导时，核对语言、模型范围、universe 与背景依赖；不暗加选择或标准性假设。
- 模型内部的自然数、有限序列和递归不一定外部标准；不能用宿主 `Nat.rec` 或外部良基性替代内部归纳。
- 存在性、唯一性、实际规格与条件接口分别陈述。消费构造契约的定理不等于证明该契约存在。
- Prop 层经典论证与 Type 层数据抽取必须区分；不要新增依赖选择的数据算子或额外对象公理。
  原有宿主基础依赖不等于对象理论采用选择公理，也不能据此声称全库不依赖选择。
- 不新增 `sorry`、`admit`、项目裸 `axiom`／`constant`、`unsafe` 或 `native_decide` 来绕过证明。
  不用关闭 linter、增加资源限制或缩小目标来掩盖问题。

## 命名与可读性

- 保持已有模块路径、命名空间和公共签名；不要为了去除上游品牌批量重命名 `YesMetaZFC.BMS`。
- 新接口沿用所在模块的 `_m`（语法／对象推导）、`_l`（语义）约定；名称描述数学作用。
- `ℳ` 为主要模型，`𝒩` 为第二模型；`Γ Δ`、`φ ψ`、`s t` 等沿用所在语言的上下文、公式与项约定。
  模型假设显式命名，如 `hℳ`、`hZF`；不要把理论前提藏进新 typeclass。
- 中文注释解释非显然的数学步骤、量词范围和前提用途，不仅复述 Lean 语法。
- 优先复用已有通用引理与证明接口；通用证明器扩展留在现有公共自动化层，不混入 BMS 专属模块。

## 保留证明的精简

- 优先级：证明有效性、数学语义、可审查性、最后才是代码行数。
- 一次处理一个相关证明族。先查调用、属性、实例、simp 用途、导入及公开文档，再做最小可逆改写。
- 保持命题、前提、量词顺序、universe、绑定范围、对象公式和公共签名。
  即使没有内部调用，有数学解释价值的接口也应保留。
- 每个小改写立即做定向检查及差异审核；阶段提交前做 Lake 验收、终局公理审计和旧资源核验。
  编译通过与语义正确分开审核；失败时修复或仅撤销该改写，不在已知失败上叠加修改。
- 按固定范围统计 Lean 物理行。文档删除、审计输出压缩与证明体精简分别报告，不用排版凑目标。
- 公理打印可集中为机器守卫，但须先证明检查覆盖与实际运行有效；不能先删旧检查再假定新检查可用。

## 构建、审计与版本保护

- 根工程与桥接工程使用各自 `lean-toolchain`；不要擅改版本、依赖锁或缓存来制造通过结果。
  桥接通过路径依赖共享根构建目录，两套工具链的构建必须串行，切换可能触发重编译。
- 完整构建入口是根目录 `bash scripts/check-all.sh`；CI 配置为 `.github/workflows/lean_action_ci.yml`。
  小批可先检查受影响模块；定向通过不能冒充完整 Lake 或远端 CI 通过。
- 保留原 `AxiomAudit.lean` 与 `SecondOrderHereditaryBMSAxiomAudit.lean` 的精确守卫。
  BMS 终局现有允许依赖为 `propext`、`Classical.choice`、`Quot.sound`；新增依赖须解释并获授权。
- `scripts/check-legacy-resources.ps1` 核验 `docs/legacy-resource-baseline.json` 中的旧资源。
  原 ZFC 模块、公开接口及 `zfc-constructible` 分支不得因新路线或精简被覆盖。
- 构建记录须注明源码状态、检查范围和实际退出结果；中止、错误或旧缓存不能记作通过。
- 保留无关脏改动，不做广泛 reset／checkout／清缓存。源码发布不带 `.lake/`、临时日志、探针或备份。
- 提交、推送与主干更新遵守本次用户授权；不要把旧指令或上游 Library 打包流程当作发布权限。
