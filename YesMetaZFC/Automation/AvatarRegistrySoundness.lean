import YesMetaZFC.Automation.AvatarSoundness
import YesMetaZFC.Automation.DAGCertificate.AvatarRegistry
import YesMetaZFC.Automation.HostRules.Semantics

/-!
# AVATAR registry 的结构检查与语义可靠性入口

registry 的覆盖检查、支持不交检查和 selector 一致性检查统一由
`DAGCertificate.AvatarRegistry` 维护；本模块不再重复声明这些 checker。
`DAGCertificate.IntrinsicReplay.AvatarSemantics` 将检查结果转换为内在字句上的
component / split 语义合同，`HostRules.Semantics.avatar_semanticallyEntailsAt`
把完整回放结果连接到宿主目标。

旧 `CheckedAvatarDAG` / raw bound-stack 路径的使用方应迁移到公共 `CheckedDAG`
和内在回放合同。导入此模块可获得上述当前接口；历史实现保留在源码包版本历史中。
-/
