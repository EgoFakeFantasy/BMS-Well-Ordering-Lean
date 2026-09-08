import YesMetaZFC.Automation.DAGCertificate.IntrinsicReplay.Avatar
import YesMetaZFC.Automation.DAGCertificate.IntrinsicReplay.AvatarSemantics

/-!
# AVATAR 可靠性入口

本入口统一导出当前内在语法回放器。旧版 raw 字句的 `SameBoundStack` / `Satisfies`
接口已随一阶语法迁移移除；继续在这里定义旧整图证明会重复公共 DAG 定义，并引用
已经不存在的环境类型。

对应证明现在位于 `DAGCertificate.IntrinsicReplay`：
* `avatarGuardedNodeTrueIn_of_supported`：带 guard 的节点可靠性；
* `rootNodeTrueIn_of_avatar_supported`：拓扑回放到根节点；
* `avatarComponentSemantics_of_checked_registry`：已检查 registry 的 component 合同；
* `avatarSplitSemantics_of_checked_registry`：已检查 registry 的 split 合同。

有限支持不交的分解定理由 `DAGCertificate.Compile.compiled_trueIn_iff_exists_component`
提供，量化统一 free registry 中的赋值。全部结论消费现有 checker 合同和 Lean 证明。
-/
