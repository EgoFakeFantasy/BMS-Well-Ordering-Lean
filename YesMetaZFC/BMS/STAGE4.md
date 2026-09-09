# BM4 良序性形式化：Stage 4

## 目标

Stage 4 对应 Hunter Theorem 2.7：从 seed 的稳定表示出发，使用 Lemma 2.5
的复制块结构与 Lemma 2.6 的有限反射，证明每个非平凡 expansion
都使表示上界严格下降，最后闭合 Stage 0 冻结的三个等价接口。

## 已完成

- `SeedStabilityData` 及其 `Fin 2` 标签函数已实现；
- seed 的严格递增、ancestor 保持和共同上界已逐项证明；
- `ExpansionLabeling` 将输出列唯一分为 `G×G`、`G×B_i`、
  `B_i×B_i`、`B_i×B_j`四个区域；
- 已证明四区域证书可组装为完整 `StableRepresentation`；
- `ExpansionLabelFamily` 已将 `G` 标签与各 `B_i` 标签组装为全列函数，
  并证明 `G`/复制块坐标的精确化简定理；
- `ExpansionRegionCertificate.labeling` 已证明八个局部顺序/ancestry 义务
  足以构造 `ExpansionLabeling`，后续反射迭代不再处理全局列号分解；
- `ExpansionReflectionState` 固定了迭代不变式：`G` 标签保持原值，
  当前最后复制块使用原 `B₀` 标签；
- `ExpansionReflectionState.reflectionInput` 已从当前表示构造第 `i` 轮
  Lemma 2.6 的规范 `X,Y,α,β`，四个边界前提全部已由严格递增与
  `m₀`-parent 的 ancestry 在 Lean 中推出；
- `successorFamily` 已实现论文的单轮重标记：早期块保留，`Bᵢ`
  使用反射图像，`Bᵢ₊₁` 使用原 `B₀` 标签；
- 已证明 `successorFamily` 的 `G×G`、`G×Bᵢ`、`Bᵢ×Bᵢ`、
  `Bᵢ×Bⱼ` 四个严格序区域；跨块证明显式使用反射见证的
  `lower_lt_image` / `image_lt_lowerBound` 字段。
- `successorFamily_preserves_good` 已闭合 `G×G` 的全行 ancestry，包括
  从非零 ancestry 反推裁剪行界并回运到原数组的边界证明。
- 已证明 `G×Bᵢ`、`Bᵢ×Bᵢ` 与 `Bᵢ×Bⱼ` 的全行 ancestry 保持；
  相邻块跨越分支显式使用 Lemma 2.5(iii)、(v) 与
  Lemma 2.6 的顶端反射字段。
- `successorCertificate` 已将八个区域证明封装为完整后继稳定表示；
- `exists_initialState`、`exists_successorState` 与 `iteratedState`
  已完成从 `A[0]` 到任意 `A[n]` 的有限反射迭代；
- `boundedExpansionRepresentation` 使用“多做一轮再去掉脚手架末块”
  构造 `A[n]` 的表示，并证明其严格受当前下边界限制；
- `expand_bounded` 已闭合 `RepresentationDescentSystem` 的总下降字段：
  非退化分支使用反射迭代，无 maximal parent 分支使用删除末列的
  前缀表示，空数组的非平凡分支被排除。
- `ReflectionWellOrderingData.wellOrderingModel` 已将 Stage 3 反射数据
  直接组装为 Stage 0 的 `WellOrderingModel`，不再把
  `expand_bounded` 作为外部前提。
- `trimZeroRows_take_trimZeroRows` 已证明规范化与列前缀的交换律；
- `zeroIterate` 已给出任意规范列前缀的精确零号 expansion 路径；
- 已证明 `A[n]` 是 `A[n+1]` 的规范列前缀，且
  `A[n+1]` 执行一个复制块长度的 `[0]` 恰回到 `A[n]`；
- 已证明同一数组的 expansion 对索引单调且两两可比，
  包括无 maximal parent 的退化分支；
- 已证明 `validSeed (height + 1)[1] = validSeed height`，从而
  所有 seed 按高度构成严格链。
- `ExpansionPath.eq_or_exists_first_step` 已证明任意非平凡路径
  可删去开头的退化边并暴露第一条严格 `Step`；
- `expansionPath_endpoints_comparable_of_accessible` 在根的 accessibility
  上归纳，结合同胞 expansion 可比性，闭合了 Hunter Lemma 2.3
  所需的有限生成闭包链性；
- `RepresentationDescentSystem.generated_comparable` 已将任意两个
  生成数组的路径提升到共同的最高 seed，并在该 seed 的
  accessibility 上得到三歧性；
- `generated_comparable` 已从 `WellOrderingModel` 和
  `ReflectionWellOrderingData` 的外部字段中删除。
- `RepresentationDescentSystem` 已证明所有生成数组都有有界稳定表示；
- 已直接对标签上界作 accessibility 归纳，证明生成数组上的
  `WellFounded GeneratedStep`；
- 已证明无限一步下降链不存在，并将良基性提升到非空有限下降；
- `WellOrderingModel` 已将三个最终定理固定为：
  `bm4_step_wellFounded`、`bm4_no_infinite_descent`、`bm4_strictWellOrder`。
- `ConstructibleStabilityFormulaData` 的二元稳定公式与 ambient 稳定公式已由
  bound/free 语法桥接、有限层真值谓词及绝对性证明具体构造；
- `stageStabilityLevyLevel_l` 用严格递增的复杂度重编号同时吸收二元稳定公式
  的统一复杂度和 ambient 公式的逐层复杂度；这一选择只使用 Lean 元层的
  `Classical.choose`，没有加入集合论公理或对象层假设；
- `OrdinalElementarityWitness.formulaLevel` 显式记录实际反射公式复杂度，替代
  上游重构前写死的 `input.level + 1`，其反射语义字段保持不变；
- `constructibleStabilityFormulaData_l` 已无条件装配上述公式、复杂度证书与
  精确满足语义；
- `reflectionData_l` 已将该具体数据实例化为完整 Stage 4 反射模型；
- 桥接项目最终导出不带公式数据参数的
  `bm4_no_infinite_descent_l` 与 `bm4_strictWellOrder_l`。

## 阶段边界

Stage 4 已闭合。组合层从 `ReflectionWellOrderingData` 得到下降、良基性、
无限下降排除与全局三歧性；模型层则由具体可构造层公式、复杂度证书、
反射和 seed 构造出该数据。最终定理不再接收
`ConstructibleStabilityFormulaData`、反射实例或其他外部证明参数。

参数化接口仍以 `reflectionDataOfFormulaData_l`、
`bm4_no_infinite_descent_of_formulaData_l` 和
`bm4_strictWellOrder_of_formulaData_l` 保留，便于替换模型；规范最终接口是
无参数的 `reflectionData_l`、`bm4_no_infinite_descent_l` 和
`bm4_strictWellOrder_l`。
