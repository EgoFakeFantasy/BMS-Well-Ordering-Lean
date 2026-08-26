# YesMetaZFC Agent Notes

本仓库的 Lean 内核采用“文献对照但不照搬有限护栏”的路线。

## 元数学内核

- 文献中类似 `2020`、`2024`、`2010` 的公式级别界限，大概率服务于纸面提纲或有限检查，不映射为核心公理前提。
- 不要把 `Formula.LevelAtMost` 加回 `Formula.IsLogicalAxiom`、`Derives`、演绎方法、全域化方法或 1.4 常用逻辑定理的主接口。
- 核心证明优先使用普通 `Derives`；不要为了复刻文献的有限护栏重新引入 `BoundedDerives` 主线。
- `Formula.level` 和 `mf1_level` 可以作为文献兼容层/审计层工具保留，但它们不应阻塞核心自动化。
- 遇到文献里的“级别不超过某自然数”“具体表达式长度”等有限护栏，默认在 Lean 核心中解除映射；只有在显式建立兼容层时才单独形式化。
- 自动化里的 Skolem 化默认使用 Lean 元层 `Classical.choice` / `Classical.choose` 封装成证书构造函数；不要向对象语言核心加入新的 `ε` 算子公理。

## 形式化习惯

- 机械 Hilbert 证明优先改进或复用 tactic，不要手写长证明序列。
- 通用自动化层放在 `YesMetaZFC.MF1.Automation` 及其子模块；`Section14` 只保留文献定理接口和旧路径兼容导出。
- 后续 CDCL、前束规划、超消元叠加演算等证明器基础设施不要下沉到具体章节目录。
- 自动化后端共用 `YesMetaZFC.MF1.Automation.Certificate` 里的公共证书内核；新增后端时优先提供 checked payload 到公共 `Node`/`Composite` 的映射。
- 一阶规范化、NNF、前束视图、Skolem 子句化属于 `YesMetaZFC.MF1.Automation.Clausification` 这样的公共前端；章节文件只消费其接口。
- 双核自动化调度放在 `YesMetaZFC.MF1.Automation.Scheduler`，负责串联 Clausification、Superposition 与 CDCL residual，不要写入 1.4 定理文件。
- 面向用户的新自动化 tactic 名称是 `prove_auto`；不要在新章节证明里继续使用旧的 `mf1_fo_core` 入口。
- residual 命题后端证书放在 `YesMetaZFC.MF1.Automation.ResidualCdcl`，优先生成 `PropResolution.CheckedUnsatCertificate` 这类可计算检查 payload。
- 证明接口优先长线复用性；如果一个限制只来自文献排版或提纲，不要传播到公共 API。
- 构建验证使用 `lake build`。
- 注释使用中文。
- 证明跑通后，再做一轮人类数学可读性清理。

## 集合论接口符号约定

- `ℒ` 固定表示纯集合论语言 `SetTheory.PureSetLanguage`，不要把它复用为任意语言变量。
- `ℳ` 表示当前主要结构，`𝒩` 表示第二个或目标结构，`𝒱` 只用于具有 ambient universe
  角色的结构。
- `𝒞` 表示 `OrderedPairConvention`，`𝕀` 表示 `𝒞.Interpretation ℳ`；多结构场景使用
  `𝕀ₘ`、`𝕀ₙ`。
- `α β γ δ ξ η θ` 默认表示序数，`ω` 默认表示满足 `ℳ.IsOmega` 的最小超限序数，
  `κ λ μ` 预留给基数；这些数学性质仍必须由 `hα`、`hω`、`hκ` 等显式假设给出。
- `Ord` 只在文献和注释中表示全体序数组成的类。Lean 接口使用 `ℳ.IsOrdinal`；
  不声明裸 `Ord` 常量，以免与 Lean 核心的 `Ord` 类型类冲突。
- `Γ Δ` 表示理论或上下文，`φ ψ χ` 表示公式，`s t u` 表示项，`F G H` 表示类函数、
  schema 或递归算子。
- 单结构理论假设使用 `hZF`、`hKP`、`hZFC`；多结构场景使用 `hℳZF`、`h𝒩ZF`。
- 结构和可推断的依赖参数默认隐式；有序对解释及模型公理证明默认显式。若 `𝒞`
  不出现在返回类型中，仍应显式传入，避免留下无法推断的 metavariable。
- 不把结构、模型公理、有序对解释、`IsOmega` 或未来的 `IsCardinal` 做成 typeclass，
  也不通过 `Classical.choose` 固定全局模型相关的 `ω`。
- 接口迁移按完整模块或完整层进行，同时更新命名参数调用；不保留旧变量名兼容层。
