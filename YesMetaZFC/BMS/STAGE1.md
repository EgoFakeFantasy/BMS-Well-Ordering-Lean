# BM4 良序性形式化：Stage 1 进度

## 本阶段目标

Stage 1 把 Stage 0 的可执行参考程序提升为可供数学证明使用的接口。参考函数仍是唯一
计算实现；本阶段只增加证明封装和规格定理，不改写 expansion。

## 已完成：合法数组接口

- `RectangularArray` 携带 `rectangular raw = true`；
- `ValidArray` 进一步携带 `trimZeroRows raw = raw`；
- `ValidArray.normalized_eq` 把结构字段还原为 Stage 0 的布尔判定；
- `certify?` 是从普通嵌套列表进入证明层的可执行检查器；
- `certify?_isSome_iff` 证明检查成功当且仅当原始数组已正规化；
- `raw_of_certify?_eq_some` 证明检查器不会改变数组。

## 已完成：parent 规格

- `greatestBelow?` 返回值严格小于搜索上界、满足谓词，并且大于等于所有其他候选；
- 搜索失败当且仅当上界以下不存在候选；
- `parent` 已等同于对 `parentEligible` 的最大候选搜索；
- `parent_some_lt`：每条 parent 边严格减小列号；
- `parent_some_isGreatest`：返回值确为最大合格列；
- `parent_eq_none_iff`：精确刻画越界或无候选两种失败原因；
- 第零行与后继行的结果均已展开成论文使用的坐标不等式；
- 后继行 parent 已证明必为低一行的严格 ancestor。

这些定理目前对任意 `BMSArray` 成立，因此对 `ValidArray.raw` 可直接使用，而且比只在
合法数组上陈述更强。

## 已完成：ancestor 的 fuel 消去

`ParentEdge` 给出直接 parent 边，`StrictAncestor` 定义为该边的非空传递闭包。
`isAncestor_iff_strictAncestor` 证明：参考程序用目标列号作为 fuel 得到的布尔结果，恰好
等价于这个无 fuel 的数学定义。证明使用 `parent_some_lt`；因此不存在 fuel 提前耗尽。

## 已完成：expansion 保持合法性

- `supportHeight` 不超过列长，且不会因在其高度以上截断而改变；
- `copyBlock` 保持每一列的长度；
- 矩形输入经过 `expandRaw` 后仍矩形；
- `trimZeroRows` 保持矩形并且幂等；
- `normalized_expand` 证明参考 expansion 将合法输入映到合法输出；
- 总函数 `ValidArray.expand : ValidArray → Nat → ValidArray` 已建立；
- `ValidArray.raw_expand` 逐定义证明其底层数组就是 `BMS.Reference.expand`。

## 已完成：生成关系

- `validSeed` 给每个有限高度的 seed 携带合法性证明；
- `ExpansionEdge` 表示允许相等的一次 expansion；
- `Step smaller larger` 表示 Stage 0 冻结的非相等下降步骤；
- `Generated` 是从全部 seed 出发、对 expansion 封闭的归纳谓词；
- `ExpansionPath` 是零步或多步的有限 expansion 路径；
- `generated_iff_seed_path` 证明归纳闭包与有限路径定义等价；
- `generated_minimal` 证明 `Generated` 的最小闭包性质；
- `StrictDescent` 是非空严格步骤的传递闭包，并保持生成性。

## Stage 1 验收结论

- [x] 数学定理接口不再以非矩形、未正规化列表为默认定义域；
- [x] parent 搜索的下降性、资格、最大性和失败条件已证明；
- [x] ancestor 的计算 fuel 已从数学接口中消去；
- [x] expansion 的矩形性与正规化保存已证明；
- [x] 合法 seed、合法 expansion、生成闭包与有限路径已建立；
- [x] 所有证明连接到 Stage 0 参考实现，没有第二套计算语义；
- [x] 默认全仓库构建通过，且 BMS 模块没有 `sorry`、`admit` 或新增公理。

Stage 1 至此完成。

## Stage 2 入口

Stage 2 进入论文 Lemma 2.5 的组合核心：建立复制块的全局列索引映射，刻画各行 parent
候选集在 `Bᵢ` 间的对应，并证明最大候选随复制保持。E06 是该阶段的主要风险；在这些
结构引理完成以前，不开始序数标签与集合论反射部分。
