# BM4 良序性形式化：Stage 2

## 权威陈述

本阶段对应 Rachel Hunter, *Well-Orderedness of the Bashicu Matrix System*,
arXiv:2307.04606v3, Lemma 2.5：

<https://arxiv.org/html/2307.04606#S2.Thmtheorem5>

设非空数组分解为 `A = G + B₀ + (C)`，`Bᵢ` 为 expansion 中的复制块，`l₀=|G|`、
`l₁=|B₀|`。需要同时归纳行号 `k` 证明：

1. `G → B₀` 与 `G → Bₙ` 的 `k`-ancestry 等价；
2. `B₀` 内部与 `Bₙ` 内部的 `k`-ancestry 等价；
3. `n>0`、`k<m₀` 时，原数组中 `B₀ → C` 与展开数组中 `Bₙ₋₁ → Bₙ[0]` 等价；
4. `Bₙ[i]`（`0<i<l₁`）的 `k`-parent 只能位于 `Bₙ` 或 `G`；
5. 对 `n₀<n₁<n`，`Bₙ₀ → Bₙ₁` 与 `Bₙ₀ → Bₙ₁₊₁` 的 ancestry 等价。

这里所有 ancestry 都使用 Stage 1 的无 fuel `StrictAncestor` 接口；最终再通过
`isAncestor_iff_strictAncestor` 回到可执行判定。

## 已完成的入口层

- `ExpansionContext` 固定 `lastIndex`、`m₀`、parent 列及其证明；
- `goodPart`、`badPart`、`blockLength` 与 `copyPosition` 已定义；
- 已证明 `B₀` 非空以及 good/bad part 的精确长度；
- 已证明参考 `expandRaw` 等于 `G ++ B₀ ++ ... ++ Bₙ`；
- 已证明 trim 不改变列数，因此 expansion 后的列数公式也成立；
- 已证明合法复制坐标在输出范围内、落在唯一块区间中；
- 已证明 `(copyNumber, localColumn)` 到全局列号的映射是单射，并随 copy 严格递增。
- 已证明全局 `copyPosition` 处取得的列精确等于相应 `copyBlock` 的局部列；
- 已定义 `copiedValue`，并证明 ascending 坐标采用线性增量公式；
- 已证明非 ascending 坐标保持原值，且第零副本 `B₀` 逐列逐项不变；
- 已证明 `G` 和 `B₀` 在 `expandRaw` 中与原数组对应位置逐列、逐项相等。
- `trimHeight` 已成为公开接口；裁剪在该高度以下保持所有 entry；
- 已证明裁剪在保留行上保持 parent 与 ancestor；
- 已证明被裁掉的行上 parent 恒为 `none`、ancestor 恒为 `false`；
- 因而 `expandRaw` 与最终 `ValidArray.expand` 的 entry/parent/ancestor 桥梁已经闭合；
- 已加入 `parent_congr` 及零行/后继行候选谓词外延定理；
- 已证明同一副本中两个坐标具有相同 ascending 状态时，共同线性偏移保持且反映严格大小。
- parent 候选条件已拆成低层 ancestry 与当前行 `entryLess` 两个可独立搬运的部分；
- 已证明对应复制列在相同 ascending 状态下保持 `entryLess`；
- 在给定低层 ancestry 对应时，零行与后继行的 `parentEligible` 均可在 `B₀`、`Bᵢ` 间搬运；
- 合法数组的矩形性已用于自动生成复制块列与行值见证，不再要求主定理手工携带 entry 存在性；
- `greatestBelow?_eq_some_iff` 与 `parent_eq_some_iff` 已给出“合格且最大”的双向规格，为下一步搬运最大候选做准备。
- 已证明同一目标的任意两个同层 ancestor 必沿同一 parent 链，因此两者线性可比；
- `AncestorBelow` 已精确定义论文集合 `I` 的“所有较低行均为 ancestor”条件；
- 已用列号严格下降排除可比性的错误方向；
- 已证明目标坐标 ascending 且候选是其同层 ancestor 时，候选坐标也 ascending；
- Lemma 2.5 的五个分句已编码为 `Lemma25AtRow`，并用 `Lemma25Below` 固定同时归纳接口；
- 已证明超出 expansion 保留高度的四个 ancestry/parent 分句自动成立；分句 (iii) 只剩证明正 expansion 保留至少 `m₀` 行。
- 已证明正编号 expansion 的裁剪高度至少为 `m₀`，因此上一项不再带任何临时高度假设；
- 已证明 parent 边以及整条严格 ancestor 链在当前行上的坐标严格增加；
- 已证明高行 ancestry 向所有低行遗传，且当前行合格候选属于论文的集合 `I`；
- 已证明两个长度不同的数组只要在目标左前缀逐项相同，该目标的所有 parent 与 ancestry 就相同；
- 因此已闭合原数组 `A`、未裁剪 expansion 和最终 expansion 在 `B₀` 上的 ancestry 桥梁；
- 已证明同层 ancestor 与目标具有相同 ascending 状态，并把 ascending 精确改写为 `B₀` 首列的非严格 ancestry；
- 已证明 `G` 后每列都存在唯一复制坐标，副本区间互不相交并严格按编号排列；
- 已把任意复制块目标的 parent 分解为 `G` 或某个不晚于目标的副本，分句 (iv) 只剩排除严格较早副本；
- 已完整证明 expansion index 为零时 Lemma 2.5 的五个分句。
- 已把当前行 ancestry 精确刻画为集合 `I` 上的“严格记录最小值”条件，并证明其充要性；
- 已完整证明 Lemma 2.5(ii)：`B₀` 与最后副本 `Bₙ` 的内部 ancestry 在所有行双向等价；
- 已完整证明 Lemma 2.5(iii)：原数组 `B₀ → C` 与相邻副本边界的 ancestry 在全部 `row < m₀` 上双向等价；
- 已证明低行 ancestry 未经过副本首列时，parent-locality 使整条链封闭在 `G ∪ Bₙ`，闭合了分句 (iv) 的“低行首列失败”分支。
- 已证明较早副本到最后副本首列的低行 ancestry 可逐边还原为原数组中的 `B₀ → C` ancestry；
- 已补全论文中省略的高行论证：最后副本首列的 `m₀`-parent 及全部 `m₀`-ancestors 均位于 `G`；
- 已完整证明 Lemma 2.5(iv)：最后副本非首列的任意行 parent 只能位于 `G` 或最后副本自身。
- 已完整证明 Lemma 2.5(i)：从 `G` 到第零、最后副本对应列的 ancestry 在所有行双向等价；
- 已完整证明 Lemma 2.5(v)：从任意较早副本到相邻两个后继目标副本的 ancestry 双向等价；
- 五个分句已组装为 `lemma25AtRow_all` 与最终定理 `lemma25_all`。

## 完成判据

- [x] Lemma 2.5(i)--(v) 全部无条件形式化；
- [x] 最终组合定理 `lemma25_all` 可直接供稳定表示构造使用；
- [x] 默认全仓库构建通过；
- [x] BMS 模块没有 `sorry`、`admit` 或新增公理。

Stage 2 已完成。下一阶段进入 Lemma 2.6 的有限反射编码。
