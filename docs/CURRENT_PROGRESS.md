# BMS 当前进度

更新日期：2026-09-28。本次快照汇总 `bm4v` 工作树、既有发布版本和 Agent Plaza
的 BMS 交付。原 ZFC／可构造证明保留其模块路径与定理签名；本次上传不是第二份
已完成的 Z₂ 良序证明。

## 已保存的成果

- 原 `FinalAssembly.bm4_strictWellOrder_l` 与 `bm4_no_infinite_descent_l`、
  可构造层次资源及 `BMSTools` 工具子库。
- 固定外部高度的载体、精确目标公式与二阶代码呈现。
- 任意 Z₂ 模型中的程序图、内部递归、数组与祖先查询、父查询、展开和标签相关规格。
- 无幂集背景中的表示、下降和良序证明资源；具体理论假设以各声明签名为准。
- 纯算术矩阵迁移、逐候选源模型迁移和完备性接线。源模型覆盖仍是显式前提。
- `PowerlessBMSQuotient{Omega,Coding,Functions,Successor,MapSpec,Arithmetic}`：
  原模型全部内部数与商 ω 的双射、集合代表、关系图提升、零与后继对应，以及真实
  加法迭代和 `additionGraph_l`。内部数允许非标准数。
- 加乘关系的真实 Z₂ 理解构造；乘法关系图及其后继步已经有接口，
  `PowerlessMultiplication.multiplication_l` 的商侧递推规格仍未完成。

## 最新交付与审查边界

Qwen 的最终算术源码为 505 行，原交付 SHA256 为
`dbeb32a00df1cf22bcba8c6a5878be8497a7903c8b5f38416eb10ffd7eb3c1a0`。
其最后一份日志记录单模块 `lake --wfail build` 成功。
WorkBuddy 的任务 62 审查覆盖 MapSpec 和较早的 262 行算术版本；
它验证了公式环境顺序、理解构造、商图与根码对应，并指出默认导入覆盖不足。
505 行版本新增的加法迭代不能沿用该报告声称已通过独立语义审查。

本次发布还修复后继图模块中的模型证明参数遗漏，并将商算术、后继图、条件迁移及
条件推导出口加入默认导入。CI 和 `scripts/check-all.sh` 增加桥工程逐模块构建，
覆盖没有被聚合入口传递导入的模块。

## 剩余证明义务

1. 证明任意商侧加法迭代输出的唯一性，并完成乘法算子及迭代规格，填满
   `PowerlessArithmetic.operations_l` 和纯算术迁移的实际乘法对应。
   当前接口不能证明这一步必须依赖完整 Collection；已有引用所需背景与最弱
   可实现背景是两个不同问题，后续仍可尝试通过 Z₂ 公式归纳直接证明。
2. 对任意 Z₂ 模型及其反例候选，实际构造候选源模型、所需公理实例与集合覆盖，
   消去 `PowerlessBMSMatrixTransfer` 和 `PowerlessBMSDerives` 的条件前提。
3. 将上述构造接到固定外部行数 H 的原目标闭句，导出真实对象层 Z₂ 推导。
   不能使用等一致性、标准模型样例或宿主 Nat 归纳代替这一义务。
4. 完成新终局的语义强度校准和独立审计，再发布用户要求的第二份完整证明版本。

## 本次验证

本次最终源码验证：`lake build BMSConstructibleBridge BMSTools BMSTools.Audit`
加上 32 个未被聚合入口导入的独立目标，退出码 0，2695 个任务完成。
最终日志中 `sorryAx` 和未完成证明警告均为零；CI 与逐模块检查脚本也拒绝这两类输出。
覆盖全部 1060 个桥接模块和聚合入口，并构建工具子库及各审计入口；
两份明确归档的历史草稿不属于这一验证范围。
`scripts/check-legacy-resources.ps1` 核验 163 个原版文件一致，
项目内导入路径的大小写检查无遗漏。根工程源码相对上一发布版本没有变化。
这是利用现有依赖缓存的验证，不是冷缓存重编译；远端 CI 状态另行查看 GitHub。
继承的 linter 警告继续显示；不关闭 linter。
逐模块检查修复了后继图环境表达式的括号及 `PowerlessCodedStageMinimalLabel`
中的弱化求值证明遗漏，后者改为复用已证明的通用公式语义引理。两份旧 API 草稿保存至
[`research/drafts/`](../research/drafts/README.md)，该目录记录实际编译失败和可用替代资源。
临时缓存、探针和日志留在本地 `.scratch/`，不进入 GitHub 源码快照。
