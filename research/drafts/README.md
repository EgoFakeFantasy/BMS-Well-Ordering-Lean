# 保留的历史研究草稿

本目录保存此前未提交、未接入默认入口且目前不能编译的两份 Lean 草稿。
它们不是可调用库或已验证的证明，CI 不将本目录作为 Lake 模块。
2026-09-28 发布前的逐模块检查确认了以下失败；源码原样保留供后续研究。

| 草稿 | 当前失败 | 已有可调用资源 |
| --- | --- | --- |
| `SecondOrderProgramReplicateEntries.lean` | 重复程序 API 未导入、`replicate_succ_l` 不匹配当前接口 | `SecondOrderProgramReplicate.entry_l`、`specification_l` |
| `SecondOrderProgramSeedSpecifications.lean` | 缺失命名空间、`numeral_val_l` 等旧接口不可见 | `SecondOrderProgramSeedSpecification.columns_l`、`width_l` 和 `SecondOrderProgramSeedEntries` |

原位置均为 `ConstructibleBridge/BMSConstructibleBridge/`。没有其他模块导入这两份
草稿；已发布资源及已验证模块的路径保持不变。
