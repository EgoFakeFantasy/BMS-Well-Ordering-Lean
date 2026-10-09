# BMS 通用证明工具子库

本库提供可复用工具；仅导入工具不等于导入 BMS 良基性或良序性终局。
子库名为 **BMSTools**，位于现有 ConstructibleBridge 工程内，
有独立 Lake 库目标、分层入口和依赖审计。它不是独立发行的无依赖软件包。

当前状态（2026-10-10）：工具已随 `main` 的 `c0db059` 发布，工程的根／桥接
CI 均通过，见 [对应 CI](https://github.com/EgoFakeFantasy/BMS-Well-Ordering-Lean/actions/runs/37917963731)。
原 ZFC 版本保留在 `zfc-constructible`；原 Z₂ 的固定高度终局由独立的
`SecondOrderHereditaryBMSWellOrder.derives_m` 提供，不隐入本工具入口。

## 使用

在 ConstructibleBridge 工程内，或依赖该工程的下游 Lean 工程内：

```lean
import BMSTools.Assignments

open YesMetaZFC.BMS.ConstructibleBridge
-- 使用 PowerlessAssignmentUpdate.exists_l、PowerlessTruthRecord.injective_l 等。
```

完整工具入口为 `import BMSTools`。优先只导入需要的分组。
声明仍保留原来的命名空间、参数及文件路径；没有复制证明、增加兼容别名，
也没有把背景假设藏进全局实例。抽取采用新增模块入口的方式，避免破坏原调用。

## 接口地图

下表的名称均在 `YesMetaZFC.BMS.ConstructibleBridge` 下。

| 导入入口 | 主要接口 | 用途与前提 |
| --- | --- | --- |
| BMSTools.Sets | PowerlessComprehension.separation_l / image_l；PowerlessCollect.exists_l | 无幂集核心模型内的纯公式分离、唯一像与非唯一见证收集；另含积、限制、函数并 |
| BMSTools.Recursion | PowerlessOrdinalInduction.induction_l；PowerlessOmegaRecursion.exists_l / unique_l；PowerlessWellRecursion.exists_l / unique_l | 内部归纳、自然数递归和依赖前驱图的良序递归；算子须有实际公式及总性、单值性 |
| BMSTools.Assignments | PowerlessAssignmentUpdate.exists_l / unique_l；PowerlessAssignmentDomain.domain_l；PowerlessTruthRecord.injective_l / monotone_l | 构造并更新集合函数赋值，控制定义域，编码三字段记录；实际函数图条件不可省略 |
| BMSTools.Certificates | PowerlessTruthCertificate.certificate_m / accepts_m / sound_l / accepts_source_l；PowerlessTruthMonotone.step_l；PowerlessTruthCertificateUnion.union_l | 检查公式、条件可靠性与二元并保持；阶段语义需要显式层及求值器假设 |

前三组适合内部集合构造、语法编码和递归形式化；第四组适合继续研究
有符号求值证书。第四组数学假设更具体，不是前三组的强度承诺。
实现文件中的完整定理类型是前提的权威来源。

当前 Assignments 分组还再导出通用的 `ParameterFusion`、`StructureCongruence`，
Certificates 分组再导出 `BoundedFormulaCertificate`，实现位于
`YesMetaZFC/Automation/`。这些接口的命名空间与前提以各实现文件为准，
不要求或宣称任意对象理论自动具有所需证书。

## 不能由本库直接得到的结论

- `PowerlessTheory.theory_m` 不含幂集与选择公理，但包含完整分离及收集。
  模块导入与 Lean 公理审计均不能替代对象理论强度分析。
- 真值证书可靠性有实际阶段、有限求值理论等前提；不是无条件全真谓词。
- `union_l` 消费已经给出的二元并成员方程，不负责在当前层收集任意证书族。
- 规则对记录集单调，不代表任意扩大的记录集仍通过整表检查。
- 含外部求值图 H 的语义有效性后置条件不能替代内部收集所需的检查公式。
- 子库入口不提供无条件接受完备性、完整有限反射、对象级 BMS 终局或
  标准 Z₃ 的强度校准。整个工程的固定高度 Z₂ 推导不能冒充本子库的无前提接口。

原 ZFC／可构造证明仍从 `BMSConstructibleBridge.FinalAssembly` 调用；
本工具入口不导入该终局，且不替换原证明。历史研究模块保留，不全数提升为推荐接口。

## 验证与维护

沿用仓库锁定的工具链与依赖。在 ConstructibleBridge 中串行执行：

```text
lake build BMSTools
lake env lean BMSTools/Audit.lean
lake build BMSConstructibleBridge
lake env lean BMSConstructibleBridge/AxiomAudit.lean
lake env lean BMSConstructibleBridge/ThirdOrderAudit.lean
```

BMSTools 是默认构建目标；仓库全检脚本另显式运行子库审计。
Audit 逐个检查工具入口传递导入的桥接声明，只允许
propext、Classical.choice、Quot.sound，并拒绝导入整库入口或 FinalAssembly。
这不是最小依赖包认证：子库仍依赖现有桥接与 YesMetaZFC 基础模块。

后续新增推荐接口须同时给出用途、完整前提、编译与公理审计结果；
不以增加包装定理或降低行数作为目标。

## 历史本地验收（2026-09-14）

以下数值及“未提交／未推送”只描述当时检查点，当前发布状态以文首为准。

- 独立工具构建通过：1396 jobs；工具依赖审计通过：3164 个声明。
- 原桥接构建通过：2241 jobs；原最终定理公理审计通过。
- 有限层 63、二阶 2845、三阶 2407、全桥 7884 个声明审计通过；
  三阶原有 62 个无规模界出口检查通过，不将其解释为强度结果。
- 原有 450 条桥接警告逐行不变，无新增工具构建警告；
  163 个冻结资源未变，492 个改动／未跟踪 Lean 文件与短路径验证树哈希一致。
- 差异检查及新子库禁止项检查通过。没有新增数学声明或修改证明正文。

使用短路径验证树串行构建。根工程与远端 CI 未重跑；
CI 和全检脚本已接入工具审计，但不将配置更新声称为远端成功。
日志保留于工作区 outputs/bms-tools-*，未提交、未推送。
