# BMS 良序性证明 Lean 形式化

## 最终结论

BM4 生成记号及其严格下降关系构成严格良序：

```lean
theorem bm4_strictWellOrder_l :
    StrictWellOrder GeneratedArray GeneratedStrictDescent
```

同时导出不存在无限一步下降链：

```lean
theorem bm4_no_infinite_descent_l :
    ¬ ∃ chain : Nat → GeneratedArray,
      ∀ index, GeneratedStep (chain (index + 1)) (chain index)
```

两个规范定理均为无参数结论。公式数据参数化版本仍被保留，便于替换模型，
但不属于最终定理的假设。

## 证明结构

- Stage 0：冻结数组、展开、下降关系与最终严格良序接口；
- Stage 1：建立表示系统、复制块与有限下降组合框架；
- Stage 2：构造可构造层级、外部 Levy 层级和固定有限层真值公式；
- Stage 3：证明稳定关系的公式内部化、复杂度界与有限反射；
- Stage 4：迭代 seed 反射，证明每次非平凡展开严格降低表示上界，进而得到良基性、
  无限下降排除和全局三歧性。

详细完成清单见 [`YesMetaZFC/BMS/STAGE4.md`](YesMetaZFC/BMS/STAGE4.md)。

## 主要入口

- `YesMetaZFC/BMS.lean`：组合证明总入口；
- `ConstructibleBridge/BMSConstructibleBridge.lean`：可构造模型桥接总入口；
- `ConstructibleBridge/BMSConstructibleBridge/ConstructibleStabilityFormulaData.lean`：
  无条件稳定公式数据；
- `ConstructibleBridge/BMSConstructibleBridge/FinalAssembly.lean`：最终定理装配。

## 构建

仓库有两个有意分离的 Lake 工程：根工程仅依赖 Lean/Std，固定使用 Lean 4.33.1；
可构造模型桥接依赖锁定提交的 Mathlib 与 `lean-constructible-universe`，固定使用
Lean 4.33.0-rc1。桥接工具链与其锁定依赖中的 `lean-toolchain` 一致，不应使用
根工程工具链强行编译桥接工程。

根工程：

```bash
lake build
```

可构造模型桥接工程使用 Lean 4.33.0-rc1，并固定远程依赖提交：

```bash
cd ConstructibleBridge
lake build
```

正常复核不需要执行 `lake update`；提交的 `lake-manifest.json` 已固定依赖版本。

仓库级一键检查会**串行**构建两个工程，并运行最终定理公理审计：

```bash
bash scripts/check-all.sh
```

在 Windows 上建议将仓库检出到较短路径（例如 `C:\src\bms`）；桥接依赖的嵌套模块名
很长，过深的工作目录可能使 Lean 无法创建 `.olean.server` 中间文件。

不要并行运行两个共享同一 `.lake/build` 的 `lake build` 进程，否则可能相互覆盖
中间 `.olean` 文件。GitHub Actions 分别在隔离 runner 中检查根工程和桥接工程，
桥接 job 明确读取 `ConstructibleBridge/lean-toolchain`。

大型证明项可能占用较多内存。在 16 GB 内存机器上建议限制为单线程：

```powershell
$env:LEAN_NUM_THREADS = "1"
lake build
```

验收时根工程与桥接工程均通过串行构建；本次短路径冷缓存记录分别为 798 和
1531 jobs。Lake 显示的 job 数会随缓存与构建 facet 状态变化，不是源码覆盖率指标。

## 证明卫生

- Stage 0–4 源码中没有 `sorry`；
- 没有 `admit`；
- 没有新增对象层公理；
- 最终两个定理的公理依赖仅为 Lean/Mathlib 标准基线：
  `propext`、`Classical.choice`、`Quot.sound`。

`Classical.choice` 只用于 Lean 元层选择有限复杂度证书，不作为新的集合论假设。

机器可复核证据位于
`ConstructibleBridge/BMSConstructibleBridge/AxiomAudit.lean`。其中的
`#guard_msgs` 不只是打印结果，还会在两条最终定理的公理集合发生变化时使检查失败。
CI 另使用 `lean-action` 的 allowlist 公理审计覆盖整个桥接命名空间。

## 来源

- YesMetaZFC 基线：<https://github.com/lanxinge/YesMetaZFC/tree/b36e2434459fa71bd6d5ff91f0882058a9746399>
- lean-constructible-universe：<https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53>

仓库保留上游历史和原始说明，新增 BMS 文件采用既有中文注释、变量名和桥接定理
`_l` 后缀规范。
