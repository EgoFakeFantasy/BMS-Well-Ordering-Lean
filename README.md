# BMS 良序性证明的 Lean 形式化

<!-- 本文件由 BMS-Well-Ordering-Lean 项目重写，替代 YesMetaZFC 上游项目介绍。 -->

本仓库使用 Lean 4 形式化 BMS（Bashicu Matrix System）第四个正式版本 **BM4 的生成记号严格良序性**。
项目包含数组与展开规则、稳定表示、可构造层级中的公式与反射，以及最终良序定理的完整装配。

本项目复用 YesMetaZFC 的逻辑与集合论基础，并在其上实现 BMS 的组合证明和可构造模型桥接；
上游来源与贡献边界见文末。

## 主要结论

最终入口位于 [FinalAssembly.lean](ConstructibleBridge/BMSConstructibleBridge/FinalAssembly.lean)，
命名空间为 `YesMetaZFC.BMS.ConstructibleBridge`。

`bm4_strictWellOrder_l` 的结论是：

```lean
StrictWellOrder GeneratedArray GeneratedStrictDescent
```

`bm4_no_infinite_descent_l` 的结论是：

```lean
¬ ∃ chain : Nat → GeneratedArray,
  ∀ index, GeneratedStep (chain (index + 1)) (chain index)
```

也就是说，规范生成的 BM4 记号在严格下降关系下构成严格良序，因此不存在无限的一步下降链。
这里的对象是源码定义的 `GeneratedArray`，不是任意整数数组。
本项目不涉及 BM4 的精确序型，也不覆盖其他 BMS 版本；规格边界见 [Stage 0](YesMetaZFC/BMS/STAGE0.md)。

两条最终定理不要求调用者提供稳定公式、反射实例或额外模型数据。
证明中间层保留了参数化接口，但最终入口已经用具体构造填满这些参数。

## 证明路线

Stage 0–4 已完成，证明分成组合层与可构造模型层：

| 阶段 | 内容 |
| --- | --- |
| Stage 0 | 固定数组、展开、下降关系及最终良序接口 |
| Stage 1 | 建立稳定表示、复制块结构与有限下降的组合框架 |
| Stage 2 | 建立可构造层级桥接、Lévy 层级与固定有限层真值公式 |
| Stage 3 | 将稳定关系内部化为公式，证明复杂度界与有限反射 |
| Stage 4 | 迭代反射构造展开后的稳定表示，使表示上界严格下降，并证明良基性与全局可比性 |

整体说明见 [BMS_FORMALIZATION.md](BMS_FORMALIZATION.md)，
逐项完成记录见 [Stage 4](YesMetaZFC/BMS/STAGE4.md)。

## 从哪里开始阅读

| 入口 | 用途 |
| --- | --- |
| [YesMetaZFC/BMS/](YesMetaZFC/BMS/) | 数组、展开、稳定表示与组合下降证明 |
| [YesMetaZFC/BMS.lean](YesMetaZFC/BMS.lean) | BMS 组合层总入口 |
| [ConstructibleBridge/BMSConstructibleBridge/](ConstructibleBridge/BMSConstructibleBridge/) | 可构造层语义、公式内部化、绝对性与反射 |
| [BMSConstructibleBridge.lean](ConstructibleBridge/BMSConstructibleBridge.lean) | 桥接工程总入口 |
| [ConstructibleStabilityFormulaData.lean](ConstructibleBridge/BMSConstructibleBridge/ConstructibleStabilityFormulaData.lean) | 最终装配所需的具体稳定公式数据 |
| [FinalAssembly.lean](ConstructibleBridge/BMSConstructibleBridge/FinalAssembly.lean) | 两条无额外数据参数的最终定理 |
| [AxiomAudit.lean](ConstructibleBridge/BMSConstructibleBridge/AxiomAudit.lean) | 最终定理的机器可检查公理守卫 |

2026-09-10 精简版本的 BMS Lean 源码为 **44,989 行、165 个文件**。
统计包含组合层、桥接层、入口及公理审计；不含上游其他源码、第三方依赖、Lake 配置、文档与构建缓存。

## 构建与复核

先安装 Lean 的工具链管理器 elan。仓库包含两个 Lake 工程，工具链由各自的
`lean-toolchain` 指定：

| 工程 | Lean 版本 | 依赖 |
| --- | --- | --- |
| 仓库根目录 | 4.33.1 | Lean / Std |
| `ConstructibleBridge/` | 4.33.0-rc1 | 根工程、锁定版本的 Mathlib 与 lean-constructible-universe |

在仓库根目录运行完整检查（需要 Bash 4 或以上）：

```bash
bash scripts/check-all.sh
```

脚本串行检查根工程全部 Lean 源模块与扫描工具，再构建桥接工程并运行最终定理公理审计。
也可以按顺序分别执行：

```bash
lake build
cd ConstructibleBridge
lake build BMSConstructibleBridge
lake env lean BMSConstructibleBridge/AxiomAudit.lean
```

仅在根目录运行 `lake build` 不等于验证了桥接层的最终定理。
正常复核请保留已提交的依赖锁文件，不需要执行 `lake update`，也不要擅自统一两套工具链。

Windows 建议使用较短的检出路径，例如 `C:\src\bms`。
在 16 GB 内存机器上，可先设置 `$env:LEAN_NUM_THREADS = "1"`。
不要同时运行共享构建目录的两个构建进程。

## 证明可信性与 CI

BMS 证明源码不使用 `sorry` 或 `admit`。最终两条定理的公理依赖为：

```text
propext, Classical.choice, Quot.sound
```

[AxiomAudit.lean](ConstructibleBridge/BMSConstructibleBridge/AxiomAudit.lean) 用
`#guard_msgs` 检查实际的 `#print axioms` 输出；公理集合变化会导致检查失败。
[Lean CI](https://github.com/EgoFakeFantasy/BMS-Well-Ordering-Lean/actions/workflows/lean_action_ci.yml)
在隔离的 runner 中分别检查根工程与桥接工程，并对桥接声明及最终定理进行公理审计。

桥接工程仍有既有 linter 警告；构建通过不代表警告已经清零。
精简工作的要求是保留数学结论与公开接口、不增加证明前提或公理，并对改动重新验证。

## 上游与致谢

- [lanxinge/YesMetaZFC](https://github.com/lanxinge/YesMetaZFC/tree/b36e2434459fa71bd6d5ff91f0882058a9746399)：
  本项目使用的逻辑、集合论与证明基础，基线为 `b36e243`。
- [05-02-07/lean-constructible-universe](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53)：
  可构造宇宙依赖，锁定提交为 `7f5a7d0`。
- [Mathlib](https://github.com/leanprover-community/mathlib4)：
  桥接工程使用的 Lean 数学库，具体版本由桥接工程的依赖锁文件固定。

本仓库保留上游 Git 历史和基础模块。BMS 相关工作集中在 `YesMetaZFC/BMS/` 与
`ConstructibleBridge/`；上游的 Rosser、不完备性等成果不作为本项目新增的 BMS 成果。

## 许可证

本项目的原创代码与随附文档采用 [Apache License 2.0](LICENSE)（`Apache-2.0`），
版权归相应作者所有，署名与来源说明见 [NOTICE](NOTICE)。

继承的 YesMetaZFC 基础代码保留上游 Apache-2.0 许可与署名。
通过 Lake 获取的 Mathlib、lean-constructible-universe 等第三方依赖仍遵循各自的许可证；
本项目的许可声明不替换第三方的许可证或权利声明。
