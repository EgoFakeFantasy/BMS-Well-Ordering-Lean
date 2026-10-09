# 两条证明路线与兼容性边界

## 已发布版本（2026-10-10）

| 版本 | GitHub 分支／数学源码基点 | 入口与交付范围 |
| --- | --- | --- |
| 原 ZFC／可构造证明 | `zfc-constructible`／`0f8e912` | `FinalAssembly.lean` 中的 `bm4_strictWellOrder_l` 与 `bm4_no_infinite_descent_l`；原完整严格良序结论 |
| 原 Z₂ 固定高度证明 | `main`／`c0db059` | `SecondOrderHereditaryBMSWellOrder.derives_m H`；每个外部 H 的无无限严格一步展开下降链对象句 |

`main` 并未删除旧版：原 ZFC 的 163 个资源 LF 内容指纹、模块路径及公开接口
保持不变。旧资源调用者可以固定 `zfc-constructible`；新资源调用者可按需导入
独立 Z₂ 模块。上传采用正常后继提交，没有强推或改写旧历史。

新入口的正式类型为：

```lean
theorem derives_m (H : Nat) :
  Derives SecondOrderArithmetic.theory_m [] (SecondOrderConcreteFormula.closed_m H)
```

没有 `hSources`、额外源模型或算术对应假设。载体是当前高度 ≤ H 的生成 BM4
数组，不限制种子高度；H 为外部模式索引。背景是完整二阶理解的原 Z₂ 呈现，
不是仅等一致的三阶／选择加强替代。`PowerlessTheory` 只作为被消去的解释中间层。
签名中的额外 pair/start/step 槽没有公理，且不进入理解正文或目标。

该对象句没有打包线性可比性，不交付对象层完整严格线性良序、内部不限高度
统一断言、最小签名独立导出或 PRA 证明码生成器 `(G)`。
三阶理论的历史研究没有因此被升级为已完成的标准 Z₃ 强度解释。

数学源码提交 `c0db059` 的本地 3993 门及最终公理守卫通过；
[远端 CI](https://github.com/EgoFakeFantasy/BMS-Well-Ordering-Lean/actions/runs/37917963731)
的 `root-build`、`constructible-bridge` 均为 success。独立 Z₂ 审计入口是
`SecondOrderHereditaryBMSAxiomAudit.lean`；旧 `AxiomAudit.lean` 仍守卫原 ZFC 终局。
具体进度及验收口径见 [CURRENT_PROGRESS.md](CURRENT_PROGRESS.md)。

## 历史路线与发布门（2026-09-13／14）

以下保持当时的研究记录；“未完成”“未发布”以及旧额度／停工描述不代表当前状态。
这些旧门限不能覆盖上面的精确交付范围，也不能据此重启历史后台任务。

> 2026-09-14 本轮收尾：按用户选择要求，已从现有研究成果提取
> BMSTools 通用工具子库，见 BMS_TOOLS.md。它不是第二份良序证明；
> 原版资源不变，下述双证明发布门仍未满足。

> 2026-09-14 最新状态：随后授权的半小时增量已完成，三阶研究
> 封存在 third-order-truth-monotone 检查点，继续保持停止。
> 未形成第二份完整证明，未满足下述发布门；本次不提交推送。

2026-09-13 用户明确要求：完成新背景证明后保留两版，旧版 ZFC／可构造
层次的资源正在被调用，不能由新路线覆盖。此前剩余 50% 的停工限制已解除。

## 原证明版本

继续保留原模块路径、公开声明及其参数：

- `ConstructibleBridge/BMSConstructibleBridge/FinalAssembly.lean` 中的
  `bm4_strictWellOrder_l`、`bm4_no_infinite_descent_l`。
- 原 `ConstructibleUniverse` 依赖、层次模型、稳定性与反射资源。
- 原根工程和桥工程的各自工具链及最终公理检查。

弱背景研究不能删除、搬迁、改名或加强这些现有接口的前提。本轮不修改
它们；之前工作树中已有的改动也不能整树回退。

`legacy-resource-baseline.json` 记录本轮恢复时 163 个既有 BM4／可构造桥
Lean 文件的当前内容哈希，包含此前未提交改动，不把基点提交误当作当前
全部内容。`scripts/check-legacy-resources.ps1` 只读检查这些资源是否改变；
新研究模块和总导入入口不在冻结清单内。此快照不代替两个最终版本的发布。

## 弱背景版本

新增资源以独立模块及独立审计入口提供。当前 `SecondOrderAudit.lean`
继续只检查原二阶路线，不导入新的三阶公理，避免把较强假设混入旧证明。

候选工作背景为第三阶算术的集合论呈现：完整分离与收集、集合良序选择、
P(ω) 存在、每个集合可单射到 P(ω)。该呈现的文献依据及尚未完成的
解释义务见 `THIRD_ORDER_BACKGROUND.md`。

这里暂取完整三阶背景的集合论呈现作为工作上界，并非已经找到严格弱于
完整 Z₃ 的充分子系统。第 5.1 节区分文献中的强度比较、实际公理使用
拆分及尚未完成的 Lean 解释；删除多余依赖本身不作为降强度成果。

`PowerlessTheory` 保留上游原公理公式而明确去掉幂集公理；
`ThirdOrderTheory` 单列新增闭句。它们不把 BM4 良序性、稳定对或反射
原则写成新公理。背景定义通过编译不等于 BM4 在该背景中已有证明。

## 最终发布门

新背景的主定理闭合、语义强度校准与独立审计完成以后，才将两条路线
正式整理成可发布的两个版本。保留一个含原接口的稳定版本，并为弱背景
版提供单独入口、依赖清单和证明范围说明；不覆盖原版本的 Git 历史。
具体采用长期分支／标签或两个发布包时，先核对现有远端状态和调用方式。
目前未创建第二个远端仓库、未发布新版本，原线上仓库未改动。
