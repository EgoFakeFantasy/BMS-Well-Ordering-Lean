# BM4 良序性形式化：Stage 0 规格冻结

## 1. 范围与权威来源

本项目只形式化 Bashicu Matrix System 的第四个正式版本 BM4。数学规格以 Rachel
Hunter, *Well-Orderedness of the Bashicu Matrix System*, arXiv:2307.04606v3
(2024-10-11) 的 Definition 1.1 和 Section 2 为基准：

- <https://arxiv.org/abs/2307.04606>
- <https://arxiv.org/html/2307.04606>

BM1、BM2、BM2.3、BM3、BM3.3、Pair Sequence System 的精确序数分析以及 BM4 的精确
order type 均不在当前项目范围内。

## 2. 冻结的数据表示

`BMSArray = List (List Nat)`。外层列表从左到右列出矩阵的列；内层列表从第 `0` 行
开始向下列出该列的坐标。因而论文中的一个 `n × m` 数组在代码中有 `m` 个外层元素，
每个内层元素长度为 `n`。

数学定义域中的数组必须满足：

1. `rectangular A = true`，即所有列等高；
2. `trimZeroRows A = A`，即底部不存在所有列均为零的行。

参考函数对任意列表都有值，但其在非矩形输入上的结果不属于数学规格。Stage 1 的定理
只对满足合法性条件的数组陈述。

空数组 `[]`、零行单列 `[[]]` 与零行双列 `[[], []]` 是不同数组。删除底部零行不会
删除列，因此该区别必须保留。

## 3. parent 与 ancestor

对合法数组 `A`、列 `i` 和行 `m`：

- `parent A 0 i` 是最大的 `j < i`，满足 `A[j,0] < A[i,0]`；
- `parent A (m+1) i` 是最大的 `j < i`，满足 `j` 是 `i` 的严格 `m`-ancestor，且
  `A[j,m+1] < A[i,m+1]`；
- 严格 `m`-ancestors 是从 `i` 开始反复应用 `parent A m` 得到的列，不包含 `i`；
- non-strict ancestry 在需要时另行定义为相等或严格 ancestry；
- 超出列高的坐标不产生 parent。

参考实现用列号作为递归 fuel。合法 parent 总是严格减小列号，所以该 fuel 足够；Stage 1
必须证明计算定义与无 fuel 的传递闭包定义等价。

## 4. expansion

`expand A n` 冻结为以下算法：

1. 若 `A = []`，返回 `[]`；
2. 令 `C` 为最后一列；
3. 令 `m₀` 为使 `C` 存在 `m₀`-parent 的最大行；
4. 若不存在 `m₀`，删除 `C`；此时 `G` 是 `C` 前的全部列且 `B₀ = []`；
5. 若存在 `m₀`，令 `p` 为 `C` 的 `m₀`-parent，`G` 是 `p` 前的列，`B₀` 是从
   `p` 到 `C` 前一列的连续 block；
6. 对 `D = B₀[j]` 和 `m < m₀`，当 `j = 0` 或 `B₀[0]` 是 `D` 的严格
   `m`-ancestor 时，该坐标 ascending；
7. `Bᵢ` 复制 `B₀`，并把每个 ascending 坐标 `D[m]` 改为

   `D[m] + i * (C[m] - B₀[0][m])`；

8. 未正规化结果为 `G ++ B₀ ++ B₁ ++ ... ++ Bₙ`；
9. 最后删除所有共同的底部全零行，但不删除任何列。

因此复制块个数为 `n + 1`。特别地，`expand A 0` 删除最后一列，保留前缀
`G ++ B₀`，随后进行零行正规化。

## 5. seed、BMS 与顺序方向

高度 `h` 的 seed 固定为：

`seed h = [replicate h 0, replicate h 1]`。

Stage 1 将使用以下归纳闭包，而不是直接把“最小偏序”作为原始定义：

```text
Generated (seed h)
Generated A  ->  Generated (expand A n)
```

一步关系的方向固定为：

```text
Step smaller larger  ↔  ∃ n, smaller = expand larger n ∧ smaller ≠ larger
```

`B ≤ A` 表示从 `A` 经有限次 expansion 可到达 `B`；`B < A` 要求路径非空。随后证明
它等于包含所有 `expand A n ≤ A` 的最小偏序。严格排除相等是必要的，因为
`expand [] n = []`。

字典序首先比较列；列不同时再逐坐标比较。真前缀严格较小。Stage 1 的目标包括：

```text
Generated A -> Generated B -> (B < A ↔ compareArray B A = .lt)
```

## 6. 最终定理的冻结陈述

最终交付必须同时闭合以下三个等价接口：

1. `WellFounded Step` 在 `Generated` 子类型上的版本；
2. 不存在 `A₀, A₁, ...` 满足每个 `Step A_{i+1} A_i`；
3. `Generated` 上由 expansion 生成的关系构成 strict well-order。

定理不声称算出 BM4 的精确 order type，也不把任意非标准数组解释为序数记号。

## 7. Hunter v3 的勘误与显式证明债务

### E01：Lemma 2.1 的空数组边界

论文写成所有 `A` 均有 `A[n] <lex A`，但 Definition 1.1 规定空数组 expansion 后仍是
自身。形式化陈述必须增加 `A ≠ []`；或者改成非严格结论，并在非空时加强为严格。

状态：局部修正，低风险。

### E02：Lemma 2.3 中 subsequence 应为 prefix

反复执行 `[0]` 只能删除末列，不能得到任意子序列。证明实际使用的是前缀关系。

状态：术语修正，低风险。

### E03：反射步骤必须保持 `ω` 下界

Theorem 2.7 把 Lemma 2.6 中的 `X` 取为 `Bₙ` 前所有标签。若 `G` 为空，这个集合也为空，
反射得到的 `Y'` 不保证仍大于 `ω`，下一轮未必满足 Lemma 2.6 的 `ω < α` 前提。
形式化版本固定使用：

`X = {ω} ∪ {Bₙ 前所有列的标签}`。

状态：必要的局部加强；必须在纸面预证明中复核其余前提。

### E04：seed 的稳定表示不能省略

论文称初始集合显然存在稳定表示并且其 `o` 值随高度严格增加。形式化必须构造对每个
有限高度同时满足所需 `α <ₘ β` 的序数对，再由 expansion 秩下降推出 seed 间的严格性。

状态：依赖有限反射，阻塞最终定理。

### E05：特殊序数 `σ` 的存在与闭包性质未展开

论文定义最小的 `σ`，使某个 `β` 对全部有限层级满足 `σ <ₙ β`，随后直接在 `σ` 以下
选择稳定标签。需要补充该 `σ` 的存在，以及有限稳定配置在 `σ` 以下充分存在的证明。

优先替代方案：有限数组只要求有限多个层级关系，直接证明“有限层级/有限图反射”，
从而避免对全层级 `σ` 的依赖。

状态：路线选择点，高风险。

### E06：Lemma 2.5 的同时归纳需要强化

原文多次使用 “trivially extended”“easily modified”。Stage 1 必须先证明 block-copy
索引映射、parent 候选集以及最大候选在复制下的行为，再把五个结论作为推论。

状态：主要组合证明债务，高风险。

### E07：生成偏序与有限 expansion 路径的等价

论文直接使用 `A' < A` 当且仅当 `A'` 由有限个 expansion 得到。形式化必须分别证明
传递闭包是偏序、包含生成边，并满足相应的最小性。

状态：常规关系论证明，中风险。

### E08：`o(A)` 的存在和最小值实现

在使用最小序数上界之前，必须证明稳定表示集合非空，并证明所取最小值确由某个稳定
表示实现。实现中优先最小化最后一列标签的 successor，而不是直接最小化任意上界。

状态：依赖 E04 和反射，中风险。

### E09：Lemma 2.6 的公式复杂度编码

需要验证 `η <ₖ Ord` 的可定义性与论文所引 Kranakis Theorem 1.8 的准确接口，并证明有限
合取、存在闭包及相对化保持相应 Lévy 层级。不能只把这些作为 Lean 外层 Prop。

状态：主要集合论证明债务，高风险。

## 8. YesMetaZFC 资产审计

已经存在并通过构建：

- 一阶公式、项、环境和满足关系；
- `IsDelta0`、`IsSigma1`、`IsPi1`；
- Lévy embedding、Delta0 双向绝对性、Sigma1 向上绝对性和 Pi1 向下绝对性；
- ZF、ZFC、KP 模型接口；
- 集合编码的序数、自然数、序数运算和超限递归；
- 良基递归和抽象秩函数。

当前缺少：

- 对任意 `n` 统一定义的 `Sigma n` / `Pi n`；
- 构造层级 `L α`；
- `L α` 之间的包含映射和传递模型接口；
- `SigmaElementary n (L α) (L β)`；
- 稳定关系 `α <ₙ β`；
- Hunter Lemma 2.6 所需的有限图反射；
- 论文引用的 `η <ₖ Ord` 复杂度定理。

因此 YesMetaZFC 足以固定 Lean 4 为目标环境，但尚未直接闭合 Stage 4。

## 9. 回归向量

`Stage0Tests.lean` 固定 26 个 expansion 输入/输出向量，覆盖：

- 高度 0–4 的 seed；
- expansion 参数 0、1、2、3、4；
- 不存在 parent；
- 单行 parent chain；
- `B₀` 含多列；
- 两行与三行 ancestry；
- 底部零行删除；
- 多副本的线性增量。

测试还统一检查：

- 输入和期望输出均正规化；
- 参考实现精确产生固定输出；
- 每个非平凡样例均按冻结字典序严格下降；
- `expand (seed (h+1)) 1 = seed h` 在前四层成立；
- 两个代表性数组的 parent 与 maximal-parent-row 值。

这些是规格回归测试，不代替 Stage 1 的一般性证明。

## 10. Stage 0 验收结论与 Stage 1 入口

Stage 0 完成条件：

- [x] 权威 BM4 版本与范围已冻结；
- [x] 数据表示、索引方向和正规化已冻结；
- [x] parent、ancestor、expansion、seed 与顺序方向已冻结；
- [x] 可执行参考实现进入默认构建；
- [x] 至少 20 个固定 expansion 向量进入默认构建；
- [x] 论文勘误与证明债务已登记；
- [x] YesMetaZFC 可复用资产与缺口已登记；
- [x] 全仓库无错误构建。

Stage 1 应从“合法数组封装 + parent 的规格定理”开始。不得先重写 expansion；只有在
证明新定义与 `BMS.Reference.expand` 对所有合法输入相等之后，才能替换参考实现。
