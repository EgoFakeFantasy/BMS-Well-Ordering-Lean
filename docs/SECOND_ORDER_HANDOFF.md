# 弱背景路线交接

## 本轮增量（2026-09-27 夜，WorkBuddy 执行 Codex task #44）

### 一、task 42：`PowerlessBMSMatrixTransfer.lean` 编译修复（已完成）

**状态：已证（严格构建通过）。**

- 文件：`ConstructibleBridge/BMSConstructibleBridge/PowerlessBMSMatrixTransfer.lean`
- 修复前 SHA256 `cdeb8ef9d47b30aa6594702c17f033a44a41797474a7d8151ae9401250878953`（有编译错误）
- **修复后 SHA256 `17a58917e3c645657ecae90ebafda428f78180bb0d8bcd3ef54d833946ed514c`**
  （9956 B / 206 行，mtime 2026-09-26 23:41:16 +1000）
- 唯一改动：**纯块移动** —— `matrix_l`（原 121–132 行）整体上移到 `matrix_at_l`（原 50–119 行）
  之前。字节数与行数不变，排序后行多重集与原文件完全相同（零内容增删）。
- 根因：`matrix_at_l` 前向引用后定义的 `matrix_l`，导致 Lean 报 `118:18 Unknown identifier 'matrix_l'`
  并在证明起点报 `58:45 unsolved goals`（**同一根因的两个症状**）。
- 验证：`LEAN_NUM_THREADS=1 lake --wfail build BMSConstructibleBridge.PowerlessBMSMatrixTransfer`
  → **rc=0，Build completed successfully (1853 jobs)，零 error**。
- 四出口 `#print axioms`（`:200–203`）均为 `[propext, Classical.choice, Quot.sound]`，
  **`sorryAx` 全部消失**（修复前 `matrix_at_l` / `closed_l` / `closed_from_candidate_sources_l` 带 `sorryAx`）。
- 独立复验：qwen3.8 已用同一命令复核（rc=0 / 1853 jobs / 零 warning / 构建前后字节指纹一致），
  并如实标注该 1853 job 为 **`Replayed`**（非冷编译）。
- 日志：`.scratch/wb-task42-build-01.log`（WorkBuddy）、`.scratch/c24_compile/task42_verify_build.log`（qwen3.8）。

### 二、`ThirdOrderAudit` 在当前源码上重跑（已完成，gate 效力恢复）

- 命令：`LEAN_NUM_THREADS=1 lake --wfail build BMSConstructibleBridge.ThirdOrderAudit`
- **rc=0，Build completed successfully (1956 jobs)，零 error**（约 3 分钟）。
- **2191 个声明的公理集全部是三项标准公理的子集**：
  1927 个 `{propext, Classical.choice, Quot.sound}`、176 个 `{propext, Quot.sound}`、
  85 个 `{propext}`、3 个 `{Quot.sound}`；**`sorryAx` 计数 = 0**。
- 与旧结论（22:55，1956 jobs）job 数逐字一致 ⇒ 审计覆盖面未缩水；且**强于旧版**
  （旧版 `closed_l` 带 `sorryAx`，现四出口全部干净）。
- 日志：`.scratch/wb-third-order-audit-after-task42.log`。

### 三、⚠️ 本轮最重要的方法论更正：`#print axioms` 干净 ≠ 不依赖对象理论公理

**本节更正了此前基于 `#print axioms` 的推断，该推断已作废。**

Lean 的 `#print axioms` **只追踪公理常量（axiom constants），不追踪定理参数（假设）**。
本项目的对象理论前提一律以函数参数传递：

```lean
(hℳ : FirstOrder.Theory.Models ℳ PowerlessTheory.theory_m)
```

它在定理类型中是**参数**，因此**完全不出现**在 `#print axioms` 输出中。
⇒「公理集只有 `propext/Classical.choice/Quot.sound`」是**平凡事实、零强度信息**。

**判定"某定理是否依赖对象理论公理"的正确流程（三层判据，均经实证）**：

1. ❌ `#print axioms` —— 只追踪公理常量，参数不出现 ⇒ 无信息。
2. ⚠️ grep 符号调用点 / **直接** import 者 —— 只能**否证**，不能**肯定**。
   反例：`PowerlessClassCore` 的直接 import 者确实不在下降链上，
   但沿 import 反向图向上爬 15 跳即可达 `PowerlessBMSWellOrder`。
   **直接调用者不在链上 ≠ 间接不在。**
   另：模块级名称可达会把**同模块内不同定理**混成一条路径（`PowerlessOrdinalCollection`
   里 `partial_l(:41)` 含 Collection、`union_l(:48)` 不含），**必须精确到定理名**。
3. ⚠️ import 闭包可达（BFS）—— 只给出**候选集**。**闭包可达 ≠ 证明体消费**。
   反例见下节：`PowerlessClassCore` 确在下降链 import 闭包内（向上可达 62 模块），
   但其证明体路径**不触达** `collection_l`。
4. ✅ **唯一可靠：逐层读证明体，确认每环返回值被解构绑定并消费到后续目标**
   （排除 Lean 中"定义存在但未被调用"的假象——未使用的 `obtain` 不会报错）。

### 四、对象理论公理的**承重性**（P2 命题，已定案）

> 注意区分两个命题：
> **P1｜"该步是否*必须*用某公理"（可消去性）** —— 需否证性证据（相对模型或编译反例）⇒ **未证**；
> **P2｜"当前证明体是否*实际消费*了某公理实例"（承重性）** —— 关于已存在证明体的**事实**问题
> ⇒ **可确定**，无需编译。
>
> **不要把 P1 的未证状态读作 P2 也未定案。**

#### （a）`PowerlessTheory.axiom_m.separation` —— **承重（已定案）**

两条独立路径，全部逐环 `sed` 打印证明体原文核对：

```
路径 1：
PowerlessBMSWellOrder.no_chain_l(:90 调 PowerlessArithmeticNumeral.numeral_l；
  :48 调 PowerlessArithmeticComprehension.models_l)
  → PowerlessArithmeticComprehension.models_l(:48/83) → comprehension_l(:145) → extension_l(:114)
    → PowerlessComprehension.separation_l(:71 调 PowerlessSeparation.exists_l)  ★消费点
      → PowerlessSeparation.exists_l(:71)
        → PowerlessTheory.axiom_m.separation φ (PowerlessSeparation.lean:22)  ★★终局
路径 2：
PowerlessBMSChainMinimum.no_chain_l(:135 调 PowerlessOrdinalMinimum.exists_l)
  → PowerlessOrdinalMinimum.exists_l(:69 调 PowerlessComprehension.separation_l)
    → 同一终局
另：PowerlessArithmeticRelation.lean:91 亦调 PowerlessComprehension.separation_l hℳ
```

`PowerlessSeparation.lean:22` 逐字：
```lean
have h₀ := (PowerlessTheory.project_l hℳ).2 _ (PowerlessTheory.axiom_m.separation φ) η.free
```

#### （b）`PowerlessTheory.axiom_m.collection φ` —— **也承重（已定案，本轮新确认）**

```
PowerlessBMSWellOrder.no_chain_l(:53 调 PowerlessArithmeticRelation.exists_l)
  → PowerlessArithmeticRelation.exists_l(:66)  ★真实消费
       obtain ⟨P, hP⟩ := PowerlessProduct.exists_l hℳ ω ω
       （该 hP 在 :95 被用于构造 G 的成员来源证明，非未使用绑定）
    → PowerlessProduct.exists_l(:87) → family_l(:79)
      → PowerlessComprehension.image_l(:87)
        → PowerlessImage.exists_l(:29)  ★★
             obtain ⟨C, hC⟩ := PowerlessTheory.collection_l hℳ φ η A h
          → PowerlessTheory.collection_l(:96)
            → PowerlessTheory.axiom_m.collection φ  ★★★终局
```

**语义要点**：`PowerlessArithmeticRelation` 的导言（`:6–10`）写明其意图是
「在内部 `ω×ω` 上分离，得到同一模型中的有序对集合」，故 Collection 的
**唯一实际数学需求 = 内部 `ω×ω`（及其行）作为集合存在**。

#### （c）`PowerlessClassCore` 路径 —— **在 import 闭包内，但证明体不消费 `collection_l`**

（本条是"闭包可达 ≠ 承重"的实证，也解释了为什么不能靠 import 分析下结论）

```
PowerlessClassCore(:82 调 PowerlessClassComprehension.collection_l)
 → PowerlessClassComprehension(:117) → PowerlessClassCollection.exists_l(:57)
   → PowerlessSourceWitnessDomain.exists_l（该文件全文无 collection_l 命中）
     → PowerlessSourceWitnessSequence(:97) → PowerlessOrdinalCollection.union_l
       → PowerlessOrdinalCollection.lean:50（union_l 体的 :46–60）：
            obtain ⟨β, hβ⟩ := PowerlessBasic.union_l hℳ A
            refine ⟨β, PowerlessOrdinal.of_transitive_l hℳ ?_ ?_ ?_, hβ⟩
          → **零 collection_l、零 Collect.exists_l**（只用 Union + 序数传递性 + 三分律）
```

补充：`PowerlessOrdinalCollection` 中真正含 Collection 的只有 `partial_l(:41 调 PowerlessCollect.exists_l)`，
其唯一调用者是同文件 `witnesses_l`，**不在下降链证明体上**；下降链实际用的是
`union_l` 与 `bound_l`，**两者证明体均不含 Collection**。同文件 `bound_l(:63)` 只用
`union_l` + `PowerlessNatural.successor_exists_l` + `PowerlessOrdinalOrder.trichotomy_l`。

### 五、Collection 依赖审计的当前精确状态（供后续裁定）

| 项 | 状态 |
|---|---|
| **P2：`axiom_m.separation` 承重** | ✅ **已定案：是**（两条独立路径） |
| **P2：`axiom_m.collection` 承重** | ✅ **已定案：是**（入口 `PowerlessArithmeticRelation.exists_l:66`，唯一数学需求 = `ω×ω` 存在） |
| **P2：`PowerlessClassCore` 路径是否消费 `collection_l`** | ✅ **已定案：否**（闭包内但不消费） |
| **P1：能否消去 / 弱化 `collection` 的全公式模式** | ❌ **未证（开放问题）**——这正是下节的"真正剩余的桥" |
| P2：`PowerlessClassComprehension.separation_l` 路径（经 `PowerlessClassSeparation`）是否承重 | ❓ **未逐环下钻** |
| P2：`PowerlessBMSStrictDescent` / `PowerlessBMSChainMinimum` 内部其余 `hℳ` 消费点 | ❓ **未穷举** |

**关键结论修正**：本交接文档此前隐含的「Collection 瘦身可优先尝试删除 Collection 依赖」
**不能**被读作"Collection 未被使用"。**它确实被使用，且位置精确（ω×ω 一处）。**
可探索的弱化方向应改为：**寻找只保证相关有限参数闭包足够的相对模型**，使这条
`ω×ω` 构造可用更弱理论完成，而不是"删除 Collection"。

### 五之二、⚠️ 「每个固定外部 H 的 Z₂ `Derives`」是否真正闭合 —— **否，且远未闭合**

（#44 步骤 E 明确要求特别说明此项，以免把语义条件桥误当作最终形式化。）

**结论：不闭合。** 精确状态分三层：

| 层 | 内容 | 状态 |
|---|---|---|
| ① 语义条件桥 | `PowerlessBMSWellOrder.models_l` / `matrix_l` / `no_chain_l` 等：**在 `PowerlessTheory` 模型内**成立 | ✅ **已证**（严格构建，`#print axioms` 三项标准公理） |
| ② Z₂ → `PowerlessTheory` 前提的桥 | 源模型构造 + 算术对应 `C` | ❌ **既未构造、也无实例** |
| ③ 无条件 Z₂ 出口 | `SecondOrderZeroHeight.derives_m`（`Derives theory_m [] (closed_m 0)`） | ⚠️ **仅 n=0**，且**落在所有 CI 路径之外**（见第六节） |

**第 ② 层的关键新证据（本轮独立验证）**：`SecondOrderPureTransfer.correspondence_l`
（`SecondOrderPureTransfer.lean:23`，**structure**，7 字段：
`numberEquiv_l` / `setRel_l` / `zero_l` / `succ_l` / `add_l` / `mul_l` / `member_iff_l`）
**在全树范围内没有任何实例构造**：
- 除定义外，仅在 `PowerlessBMSMatrixTransfer.lean:44/53/66/142` **作参数出现**；
- `SecondOrderRestrictedQuantifier.compiled_matrix_correspondence_l:173` 名字相似，
  但返回类型是 **Prop 双向真值**（`Formula.satisfies ... ↔ ∀ X, P X → ...`），
  **不是** `correspondence_l` structure；
- ⇒ **task42 的四个出口（`matrix_l` / `matrix_at_l` / `closed_l` /
  `closed_from_candidate_sources_l`）目前没有任何调用方可以满足其输入**，
  包括 `C` 本身与 `closed_l` 的 `hCover` 前提。

**供给侧 vs 需求侧的精确差集（逐项对齐，勿只记"少一条"）**：

| `PowerlessTheory.axiom_m`（需求，`:38-46`） | `SecondOrderWeakSetTheory.axiom_m`（供给，`:23-32`） | 状态 |
|---|---|---|
| extensionality | ✅ | 句子编码需逐条对上 Project 包装（**未做**） |
| empty | ✅ | 同上 |
| pairing | ✅ | 同上 |
| union | ✅ | 同上 |
| infinity | ✅ | 同上 |
| foundation | ✅ | 同上 |
| separation φ | ✅（完整分离） | 同上 |
| **collection φ** | ❌ **无** | **确定缺口** |
| — | 多出 `transitive`（传递超集） | 供给侧更强，不影响 |

⇒ 「Z₂ → 背景的缺口恰为 Collection 一条」这一判断**方向正确**，但**前提是上表 7 条能逐条
对上 Project 包装**——该对齐**尚未做过**，必须单列为待办，不得并入已收敛。

**尚存的候选路线（本轮未决，留给 Codex 裁定；不在 #44 授权范围内自选）**：
- **A**：证图商满足下降所需的那些 Collection 实例。因 Collection 的唯一数学需求
  = **内部 `ω×ω` 作为集合存在**（第五节已定案），故 A 只需在 TMC 里造出 `ω×ω`
  （TMC 有可数性 + Mostowski 坍缩 + 传递超集可用），**无需**满足完整 `collection φ` 全公式模式。
  **本路线面最小。**
- **B**：把下降链前提整体弱化到 `SecondOrderWeakSetTheory.theory_m`（即链级改前提）。
  **成本最高。**
- **C**：走 `ThirdOrderStageCore.models_l`（满足**完整** `PowerlessTheory.theory_m`，
  但前提换成 `ThirdOrderTheory`），另找 Z₂ → `ThirdOrderTheory` 通道。
  **本轮未找到现成定理**（标注"未找到"，非"不存在"）。
- **正交必经工作**：无论 A/B/C，都需要有人构造 `correspondence_l` 实例
  （数域 ≅ + `setRel` 覆盖），此项与 A/B/C 正交。

### 五之三、P3（「`ω×ω` 是否为该链唯一 `collection_l` 消费点」）—— 覆盖面与结论

> **⚠️ 本节结论经三轮迭代，现行为第三版（2026-09-27 01:00 AEST）。**
> 第一版（#2997）与第二版（#3003）的"两条入口、唯一需求 ω×ω"**已被推翻**，
> 错因是 BFS 设 `maxdepth 15` 而真实路径最长 **21 跳**，被深度上限截断。
> 第三版基于**严格模块限定解析、CAP=60 的机械穷举**。以下为**现行有效**版本。

**（1）覆盖面（程序化、可复现）**

范围 = `PowerlessBMSWellOrder.no_chain_l` 的**证明体依赖闭包**（不是 import 闭包）：

| 指标 | 第一版（maxdepth 15） | **第三版（CAP=60，严格模块限定解析）** |
|---|---|---|
| 闭包声明数 | 426 | **2409** |
| 可达的直接 `collection_l` 调用点（去自环） | 2 | **4** |
| 最长真实路径 | （被截断） | **21 跳** |
| 解析口径 | 裸名（有多义假阳性） | **模块限定优先，裸名只解析本模块** |

**（2）机械穷举结果：4 个入口、2 类独立消费点**

| # | 入口声明 | 距 `no_chain_l` | 调用到的 `collection_l` 声明 | 是否经 `image_l` |
|---|---|---|---|---|
| ① | `PowerlessImage.exists_l:29` | **5** | `PowerlessTheory.collection_l:96` | 自身（即该点） |
| ② | `PowerlessOracleSupport.sentence_l:103` | **7** | `PowerlessOracleSupport.collection_l:44` | 否，但**经 ③** |
| ③ | `PowerlessCollect.exists_l:25` | **10** | `PowerlessTheory.collection_l:96` | **否（独立闭包）** |
| ④ | `PowerlessClassCore.models_l:82` | **11** | `PowerlessClassComprehension.collection_l:77` | **是（最终仍汇聚 ①）** |

**关键事实（程序验证，非推测）**：
- **①的数学需求 = 内部 `ω×ω`**：路径
  `no_chain_l:53 → PowerlessArithmeticRelation.exists_l:64 → PowerlessProduct.exists_l:84/row_exists_l:43
   → PowerlessComprehension.image_l:74/87 → PowerlessImage.exists_l:29 → PowerlessTheory.collection_l`；
  其中 `PowerlessTriangular.exists_l:24` 显式调 `PowerlessProduct.exists_l hℳ ω ω`。
- **③是真正的第二条独立支路**：`PowerlessCollect.exists_l` 的证明体闭包**不含**
  `PowerlessComprehension.image_l` 与 `PowerlessImage.exists_l`（程序判定 `False`），
  它经 `PowerlessComprehension.binary_l/binary_m` **直接调 `PowerlessTheory.collection_l`**（φ = `binary_m φ`）。
  ⇒ 这是与 `ω×ω` **无关**的第二类公理需求。
- **②经③，④经①**（不是第三类）：
  - ②：`OracleSupport.collection_l:51 → PowerlessOracleClosure.collect_l:140 → PowerlessCollect.exists_l:25`；
  - ④：`ClassComprehension.collection_l:117 → PowerlessClassCollection.exists_l:57
     → PowerlessSourceWitnessDomain.exists_l:79 → PowerlessSourceWitnessSequence.exists_l:52
     → PowerlessOmegaRecursion.exists_l → PowerlessComprehension.image_l:38 → PowerlessImage.exists_l:29`。
    程序验证：`PowerlessClassCollection.exists_l` 的闭包（437 声明）**可达 `image_l` = True**。

**（3）现行结论（第三版）**

> 在 `no_chain_l` 的**完整证明体依赖闭包（2409 声明，CAP=60）**内，
> 消费 `collection_l` 家族的有 **4 个入口**，但**数学上只有 2 类独立的公理需求**：
> **（Ⅰ）内部 `ω×ω` 存在**（经 `PowerlessImage.exists_l:29`，入口 ①、④），
> **（Ⅱ）某二元公式 φ 的收集**（经 `PowerlessCollect.exists_l:25`，入口 ③，②汇入 ③）。
> **`ω×ω` 不是唯一消费点。**

措辞限定：grep 与 BFS 均只能**否证**、不能**肯定**；此为"在 2409 声明闭包内观察到 4 入口 / 2 类"，
非"证明不存在更多"。

**（4）⚠️ 三轮迭代的教训（方法层面，务必保留）**

1. **深度上限会静默截断真相**：第一版 `maxdepth 15` 漏掉 21 跳的 ③。
   ⇒ 穷尽性取证**不得设会截断的深度上限**，或必须报告"被截断"。
2. **裸名多义解析产生假路径**：第一版把裸名 `collection_l` 解析到**所有**同名声明，
   造出 `no_chain_l → PowerlessCollect.exists_l`（2 跳）这类**不存在**的短路径。
   ⇒ 必须**模块限定优先、裸名只解析本模块**。
3. **同名定理 ≠ 同一行为**：`PowerlessOrdinalCollection.bound_l:63`（Collection-free，
   只用 `union_l`+后继+三歧性）与 `witnesses_l:77`（消费，`:88` 调 `partial_l`）是两个不同定理；
   而 `PowerlessTruthReflection.exists_l` 在 `:68` 调前者、`:84` 调后者。
   ⇒ "该文件只有子串假阳性"与"该定理不消费 Collection"**两条都不能由文件级 grep 推出**。
4. **返回值消费检查不可省**：`no_chain_l:53` 的 `hG`、`:55` 的 `hInitial` 必须在
   `:59`/`:61` 被解构消费，路径才算"承载"。

**（5）对路线 B 的成本影响（据第③类需求）**

路线 B「弱化链前提以避开 Collection」**不能只消一个点**：需同时消
**（Ⅰ）`ω×ω`** 与 **（Ⅱ）`binary φ` 收集**两类；字面消费点是 3 个不同声明
（`PowerlessImage.collection_l` 家族 / `PowerlessCollect` / `ClassCore.models_l`），
但数学上是 2 类公理需求。路线 A 不受影响。

---

**（附）第二版遗留：对 qwen3.8 #2995 候选清单的纠正（仍有效）**

其 `p3_candidate_files.json` 给出 19 个"含 `collection_l` 字面"的候选文件。我方程序化核对
（全树 `ConstructibleBridge/**/*.lean`，排除 `.lake/`）结论：

- **① 其清单与字面 grep 不等价，且方向不一致。** 按字面 `collection_l` 检索，全树只有
  **10 个**文件命中；其中 **2 个不在其 19 清单内**：
  - `ThirdOrderStageComprehension.lean`（`:78` **定义** `collection_l`）；
  - `ThirdOrderStageCore.lean`（`:86` **调用** `ThirdOrderStageComprehension.collection_l`
    —— 这是一个**真实的 `collection_l` 调用点**，被其清单漏掉）。

  这两个文件都在 `PowerlessBMSMatrixTransfer` 的 702/703 文件前向闭包内，属 P3 应考察范围。

- **② 其清单同时过宽（且经二次复核后比初判更宽）**：13 个文件
  （`FixedHeightPureFormula`、`PowerlessArithmeticComprehension`、`PowerlessClassCollection`、
  `PowerlessOmegaRecursion`、`PowerlessOracleClosure`、`PowerlessOrdinalCollection`、
  `PowerlessOrdinalMinimum`、`PowerlessSourceReflection`、`PowerlessSourceWitnessBound`、
  `PowerlessSourceWitnessSequence`、`PowerlessTruthClosure`、`PowerlessTruthReflection`、
  `PowerlessTruthStage`）经**大小写不敏感全文复核**：
  **无一含 `collection_l` 字符串**。其 `collection` 命中全部属于以下三类，与 `collection_l` 无关：
  - **子串假阳性**：`PowerlessOrdinalCollection`（**模块名**中含 "Collection"）
    —— 命中行形如 `PowerlessOrdinalCollection.bound_l hℳ` / `.witnesses_l` / `.union_l`，
    是**调用另一个不同模块**，不是消费 `collection_l`；
  - **注释/导言**：如 `PowerlessOmegaRecursion.lean:7`「先以完整 Collection 和 Separation…」、
    `FixedHeightPureFormula.lean:47`；
  - **namespace 行**：如 `PowerlessClassCollection.lean:11/:67`。
  ⇒ 尤其 `PowerlessOrdinalCollection` 自身（`:39` 用 `separation_l`、`:41` 用 `PowerlessCollect.exists_l`）
  是被**误当成** `collection_l` 消费点，实际上它的名字里只是"Collection"这个词。

- **③ 正确做法的建议**：P3 候选集应当是「**证明体内出现 `collection_l`
  或 `axiom_m.collection` 且该声明位于目标闭包内**」的声明集合，并在报告里
  逐条给出 `文件:行:声明名`，而不是"含该字面片段的文件"。按此标准，
  当前真正需要追的消费点只有 **3 处**：
  `PowerlessImage.lean:29`（`PowerlessTheory.collection_l`）、
  `PowerlessCollect.lean:25`（`PowerlessTheory.collection_l`）、
  `PowerlessTheory.lean:96`（`axiom_m.collection φ`，即公理本身的接口），
  加上 `ThirdOrderStageComprehension.collection_l` 的定义与其在
  `ThirdOrderStageCore.lean:86` 的调用（**第三方分支**，不在 `no_chain_l` 链上）。

**（6）P3 的定级（第三版）**

| 格 | 内容 | 定级 |
|---|---|---|
| P1 | 该步是否**必须** Collection／可否消去 | **草案**（需外部落款模型；未证） |
| P2 | 现证明体**是否**消费 `collection_l` | **已证 = 是**（4 入口、2 类独立消费点，机械穷举） |
| P3 | `ω×ω` 是否为该链**唯一**消费点（穷尽性） | **否 —— 至少 2 类独立消费点**（Ⅰ `ω×ω` 经 `PowerlessImage.exists_l`；Ⅱ `binary φ` 收集经 `PowerlessCollect.exists_l`，独立于 `image_l`）|

### 六、⚠️ 待决覆盖缺口（本轮发现，未修，转交裁定）

**`SecondOrderZeroHeight` 落在所有 CI 路径之外。**

- `SecondOrderZeroHeight.derives_m`（该文件 `:55`）
  = `Derives theory_m [] (SecondOrderConcreteFormula.closed_m 0)`
  是**目前唯一无条件的 Z₂ 级推导出口**（无 `hℳ` 参数、无候选源模型条件；
  经 `SecondOrderCompleteness.derives_m` 走普通 Hilbert 推导，**不走 Powerless 下降链**）。
- 但：全树 grep `SecondOrderZeroHeight` 只命中其自身 `:15`/`:62`（无任何 import）；
  聚合入口 `BMSConstructibleBridge.lean`（562 条 import）不含它；
  `scripts/check-all.sh:26` 的 `lake build BMSConstructibleBridge`（默认目标 = 根模块闭包）
  与 `:32` 的 `ThirdOrderAudit` 都不经过它。
- **风险**：当前 CI 全绿**不代表**这条唯一无条件成果仍被编译覆盖。
- **建议改动（两行，纯构建配置，不动证明与接口）**：
  - `scripts/check-all.sh` 的 ConstructibleBridge 段追加
    `lake --wfail build BMSConstructibleBridge.SecondOrderZeroHeight`；
  - **并且**把 `import BMSConstructibleBridge.SecondOrderZeroHeight` 加入聚合入口
    `BMSConstructibleBridge.lean`（否则任何 `lake build BMSConstructibleBridge` 仍会漏掉它）。
- 该改动涉及 `check-all.sh` 与聚合入口，均属"受控脏跟踪文件"，**本轮未执行**（非本轮写域）。

### 七、本轮未做 / 未核（不要把本轮读作全门通过）

1. 全桥**默认目标**（含 `BMSTools`、`AxiomAudit`、`FiniteBoundaryAudit`、`SecondOrderAudit`）
   本轮**未重跑**；
2. CI 脚本 `scripts/check-all.sh` 本轮**未运行**；`SecondOrderZeroHeight` 缺口**未修**；
3. 上述第五节两条 ❓ 项（`PowerlessClassSeparation` 路径、`StrictDescent`/`ChainMinimum`
   其余 `hℳ` 消费点）**未逐环穷举**；
4. 本轮**未构造**任何候选源模型，**未导出**任何新的对象理论 `Derives`；
5. P1（Collection 可否弱化）**未证**，不得据本轮任何结论声称"Z₂ 路线已完成"。

### 八、本轮证据与日志索引

| 内容 | 位置 |
|---|---|
| task42 修复日志（rc=0 / 1853 jobs） | `.scratch/wb-task42-build-01.log` |
| ThirdOrderAudit 重跑日志（rc=0 / 1956 jobs） | `.scratch/wb-third-order-audit-after-task42.log` |
| qwen3.8 复验构建日志（rc=0 / 1853 jobs / Replayed） | `.scratch/c24_compile/task42_verify_build.log` |
| **`SecondOrderZeroHeight` 冷编译日志（rc=0 / 1123 jobs / Built 34s，非 Replayed）** | `.scratch/c24_compile/zeroheight_cold_build.log`（183008 B，qwen3.8 #2995 产出） |
| **P3 候选清单与逐声明命中（含本报告五之三的纠正对象）** | `.scratch/c24_compile/p3_candidate_files.json` / `p3_collection_hits_by_decl.json` |
| task41 承重性审计报告（含勘误 2 + §7 全节 + 复现命令） | 用户工作区 `workbuddy-tasks/task41补充_实际CollectionSeparation实例链路.md`（**未写入本仓库**） |
| 广场记录（前期） | 求助台 #2949 / #2971 / #2975；经验库 #2951 / #2979；茶馆 #2961 / #2965 / #2981；状态板 id 2963 / 2977 |
| **广场记录（2026-09-26 22:00 – 09-27 00:15 段）** | 茶馆 #2983（qwen3.8 五条实证）/ #2985（同上·续）/ #2991（我方复核 #2983）/ #2993（qwen3.8 接槽 + 提 P3）/ #2995（qwen3.8 冷编译交付 + P3 覆盖面）/ #2997（我方 P3 答复 + 清单纠正）；求助台 #2987（我方 #44 进度报告） |
| **`correspondence_l` 无实例证据** | `SecondOrderPureTransfer.lean:23`（structure 定义，7 字段）；调用点仅 `PowerlessBMSMatrixTransfer.lean:44/53/66/142`（作参数）；全树无实例构造 ⇒ 见第五节表第 ② 层 |
| **`SecondOrderZeroHeight` CI 覆盖缺口证据** | 全树 grep `SecondOrderZeroHeight` 只命中其自身 `:15`/`:62`；`BMSConstructibleBridge.lean`（562 import）不含；`scripts/check-all.sh:26/:32` 不经过 ⇒ 见第六节 |

**本节时点**：2026-09-27 00:20 AEST（09-26 14:20 UTC）。此后至 09:30 的增量另见下节。

## 当前恢复点（2026-09-26）

用户已取消额度停止线和“每阶段停一停”的要求。下列 2026-09-14 停止记录仅为历史，
不能作为当前停工指令。项目仍是固定外部行数的 Z₂ 逐实例证明，最终闭句尚未证明；
本地工作区为 `C:\Users\17857\Documents\Codex\bm4v`，当前修改未提交或推送。

### 本轮最新增量：无幂集背景中的完整固定行数证明

已严格构建 `PowerlessBMSWellOrder.models_l`：对任意 `PowerlessTheory` 模型，
其由内部 ω、零元及加乘运算定义的算术约化，均满足同一个原始
`SecondOrderConcreteFormula.closed_m H`，其中 H 是任意固定外部自然数。证明从原矩阵的
任意内部反例实数抽出实际内部数组链，选取链中可表示数组的最小序数上界，并由真实
严格展开构造更小上界，导出矛盾；链下标、宽度和复制次数仍允许非标准内部值。

验证记录：`lake --wfail build BMSConstructibleBridge.PowerlessBMSWellOrder` 成功，
1851 jobs（38 秒）；新终端出口 `no_chain_l`、`matrix_l`、`models_l` 的 `#print axioms`
均仅为 Lean 标准的 `[propext, Classical.choice, Quot.sound]`，无 `sorryAx`。依赖此出口的
新模块包括 `PowerlessBMSInitialSplit`、`PowerlessBMSCopyStep`、`PowerlessBMSCopyState`、
`PowerlessBMSExpansionDescent`、`PowerlessBMSStrictDescent`、`PowerlessBMSChainMinimum` 与
`PowerlessBMSWellOrder`；这些目标已有独立严格构建记录。

本次新增并接入 `BMSConstructibleBridge.lean` 与 `ThirdOrderAudit.lean` 的两个接口为：

- `SecondOrderPureTransfer.formula_l`：对 `pure_m` 公式证明跨算术结构的真值等价；数项由
  算术对应传递，集合自由变量由逐项成员关系对应传递。严格构建成功，公理为
  `[propext, Quot.sound]`。
- `PowerlessBMSMatrixTransfer.matrix_l`：把已证明的 Powerless 背景矩阵定理迁移到另一个
  二阶算术结构，但前提明确要求给出 Powerless 模型、算术对应和相关环境（其中含候选
  集合的成员关系对应）。严格构建成功，公理为
  `[propext, Classical.choice, Quot.sound]`。它是条件式迁移，不构造所需模型。
- `PowerlessBMSMatrixTransfer.closed_l`：从上述矩阵迁移推出原始固定高度闭句的真值迁移。
  它只要求同一个源模型/算术对应覆盖每个目标集合候选；标准高度数码相容已由零／后继
  同态作普通自然数归纳在定理内部推出，不再暴露为调用者前提。模块严格构建成功；该出口
  已纳入第三阶审计，无 `sorryAx`，公理仍仅为三项标准公理。它只隔离模型构造接口，没有
  提供候选覆盖或 Powerless 模型构造。

最终正式审计命令 `LEAN_NUM_THREADS=1 lake --wfail build
BMSConstructibleBridge.ThirdOrderAudit` 成功，1956 jobs（约 2 分钟）；审计报告为 3300 个声明、
220 个正向出口，未导入旧可构造语义，仅依赖三项标准公理。日志中三个跨结构新出口均无
`sorryAx`；`formula_l` 仅依赖 `[propext, Quot.sound]`，两个 BMS 迁移出口仅依赖
`[propext, Classical.choice, Quot.sound]`。全桥其余默认目标（包括 BMSTools 与其他专门
审计）本轮尚未重跑，故不宣称全默认目标门全通过。本轮单线程运行；未终止其他工作区
Lean/Lake 进程。

重要边界：上面的终局只是在含 Separation、Collection、Foundation、Infinity 等公理的
`PowerlessTheory` 背景模型中成立；该理论不含 Power Set，但仍明显强于 Z₂，且不是
Z₂ 的 `Derives` 定理。真正剩余的桥是：从任意 Z₂ 模型 M 与任意实数 X，构造一个可用的
`PowerlessTheory`（或足够弱、仍可运行当前下降证明的理论）模型 N，并给出保持数零、
后继、加、乘及指定实数成员关系的算术对应。已有 `SecondOrderTMC.models_l` 不能单独补足
Collection；也不能未经证明便把整个 `L^M[X]` 当作满足 Collection 的模型。纯公式真值
传递和矩阵条件式迁移现已形式化，但还没有候选模型构造，也没有导出 Z₂ 的对象理论
`Derives`。下一步应先精确比较下降证明实际使用的 `PowerlessTheory` 公理与 TMC/相对
构造层次中可得的公理，优先尝试删去 Collection 依赖或证明只对相关有限参数闭包足够的
相对模型；之后才把 `matrix_l` 的环境对应实例化为任意 Z₂ 模型中的反例候选。任何
“Z₂ 路线完成”的报告必须同时给出这一模型构造和最后的对象理论推导。

本轮真实程序语义进展：

- `SecondOrderProgramExpansionParentLocalityAllRows.all_rows_l`：Hunter 2.5(iv)，所有内部行、
  所有实际副本的非首列父局部性；严格构建通过。
- `SecondOrderProgramExpansionGoodToLocalAllRows.all_rows_l`：Hunter 2.5(i)，好前缀到任意
  副本局部列的全行对应；严格构建 1214 jobs 通过。
- `SecondOrderProgramExpansionInsideCopiesAllRows.member_congr_l`：补齐 Hunter 2.5(ii) 的
  高度外行，消去公共行界及坏块见证；严格构建 1162 jobs 通过。
- Hunter 2.5(iii) 继续复用 `SecondOrderProgramExpansionBoundaryActual.member_congr_l`。
- `SecondOrderProgramExpansionEarlierToSuccessive.member_congr_l`：Hunter 2.5(v)，较早副本
  到相邻后续副本的同编号目标全行对应；严格构建 1202 jobs 通过。

以上新增出口均已打印公理依赖，仅 `propext / Classical.choice / Quot.sound`。
它们是任意 Z₂ 模型内的实际算法关系定理，不是最终固定行数良序闭句的证明。
`SecondOrderProgramExpansionCrossingSource.source_iff_l` 的更强原数组刻画已通过严格构建
1211 jobs；相邻副本对应现直接复用该刻画，证明主体缩短为 9 行。
最新 `ThirdOrderAudit` 严格构建为 1917 jobs；完整桥接、BMSTools 及五项专门审计
共 2622 jobs 成功，原有 450 条警告未增加：
3162 个三阶声明仅依赖三项标准公理，202 个正向出口没有重新引用全集规模界；
未导入旧可构造语义。这不是二阶背景强度校准。实时恢复状态以 Agent 广场 bm4 状态板为准。

构建使用同一工具链 `v4.33.0-rc1`，设置 `LEAN_NUM_THREADS=1` 并串行运行；根与桥共享
依赖缓存。日志在 `.scratch/bms-*-build.log` 与 `.scratch/bms-lemma25-background-audit.log`。
不要使用外部 `Nat` 归纳遍历内部行、列或副本；新双归纳接口是实际纯公式上的
`SecondOrderProgramPrefixBlockAgreement.induct_l`。

标签路线已经新增并严格验证五个模块：

- `PowerlessBMSPrefixRepresentation`：前缀表示的实际纯公式、限制、祖先传输与全宽封口。
  不把标签域长当作数组宽度；单模块 1652 jobs。
- `PowerlessBMSExpansionInitialLabels`：把原非末列标签限制到最终展开并降低上界；
  `fallback_l` 已闭合无最大父行分支的完整表示严格下降。单模块 1717 jobs。
- `PowerlessShiftedRestriction`：实际集合函数的平移限制、域外规格、按坐标读回及递增性；
  单模块 1241 jobs。
- `PowerlessBMSLabelBlock.exists_l`：从原表示实际截取 `[p,j)` 标签块，标签在 `[α,β)`。
- `PowerlessBMSRelabelCrossing.edge_l`：真实跨副本祖先边在反射块到恢复块的标签图上保持稳定性；
  消费实际原数组刻画和同一反射图，不再假设所需两条源祖先边。

五者已纳入上述 1913 jobs 的严格背景审计。后续新增
`SecondOrderProgramExpansionPrefixToSuccessive.all_rows_l` 已通过严格构建 1220 jobs：
用内部带余除法把整个旧前缀的祖先观察归约到好前缀／较早副本，服务标签更新。
它已纳入最新完整门；有限层 79、二阶呈现 2845 声明审计亦通过。

随后 `PowerlessBMSPrefixReflection.image_l / exists_l` 已严格构建 1654 jobs：
从当前 `f+g` 前缀表示实际构造反射图及 `u=f+h`，证明 `u` 保留全部祖先边，
不再要求调用者先给出反射见证或层系统。该模块已接入聚合入口和审计。

`PowerlessNumeralOrder` 已证明标准数码的序对应及固定标准界以下的成员解码；
`bounded_l` 无公理依赖，只消耗显式零和后继语义，不能用于任意内部上界。
`PowerlessBMSParentStability.exists_l` 从真实父边、有限高度界和原表示实际取出父列／
末列标签及其正确预算层稳定对。二者均纳入最新 2622 jobs 完整门。
`PowerlessBMSRelabelCrossing.edge_l` 因而已改为自动从跨边的低行界定位 Θ 中所需层号，
调用者只交实际最大父行数码和原 Θ 的完整规格，不再手动提供某个具名层。

已完成固定一次最终展开 `y` 的整个内部复制归纳：维持副本号 `t` 上的状态 `r=p+d*t`，旧前缀图
`f:r→α`，固定原块 `g:d→β`，且拼接 `f+g` 是 `y` 的 `r+d` 列前缀表示。
实际反射产生 `u=f+h:(r+d)→α`，恢复原块后 `v=u+g:(r+2*d)→β`。
对 `t<k`，下一状态来自 `v`；在 `t=k`，只需证明 `u` 的全部边并按真实总宽封口，
不需要把不存在的额外副本算入 `y`。`u` 内部全部标签边和其存在性已经闭合；
恢复块 `g` 后的三类边通过 `PowerlessBMSPrefixRestoration.step_l` 严格验证；初始拆分、
实际复制步、纯公式内部归纳、严格下降、最小链上界及原矩阵反例排除均已接成
`PowerlessBMSWellOrder.models_l`。这些标签构造仍要求完整 `PowerlessTheory`，不能将之
冒报为 Z₂ 背景降阶已完成；对象理论 `Derives` 仍待完成。

## 历史：固定行数的 Z₂ 逐实例研究（2026-09-14）

## 历史停止记录（2026-09-14，已被后续恢复指令解除）

最新实时额度普通 codex usedPercent=60，剩余40%；按用户要求停止证明工作。
不要因目标自动续行而绕过该停止要求；须用户明确允许恢复。
最后完整验证基点仍为下述2302 jobs／全桥8501声明。随后本轮仅新增
PowerlessSourceReflectionFamily.lean（两树均已写入），尝试合并原公式
列表的真实子公式请求，构造共同反射层。尚未接入默认构建或审计；
其单模块构建在停止线触发后已中断，不能宣称验证通过。没有新增证明
缺口占位符，但当前尝试本身未完成核验。未提交或推送。
继续方向：需要同一层既满足真值有限支持又反射实际部分真值源公式。
SourceFiniteReflection/ReflectionTotal 是“稳定性推出反射”的方向，
不能循环用于稳定对存在性。SourceReflectionFamily 候选从实际请求
闭包构造反射层；其中自由参数固定，欲覆盖全部代码和赋值须把相关
槽放到绑定变量中，不能把固定自由环境误报为全参数反射。

## 最后完整验证检查点

任意外部有限部分真值族及其实际共同高层已完成。
PowerlessNumeral 定义真实内部数码关系，证明存在性、自然数性质、唯一性；
PartialTruthFinite.source_l 由零层与 Step.source_l 按外部 Nat 递推，
消去前驱正确性假设，只消费 j<k 的实际有限引入支持。TruthFiniteStage
的 formulas_m k 收集 range k 对应的原 oracle_m(formula_m j)；exists_l
调用原 TruthStage.exists_l 构造任意指定序数之上的共同真极限层，
返回所有 j≤k 的实际数码及原 formula_m j 的匹配极性双向正确性。
覆盖各层全部内部分类码与层内有限赋值，不假设内部 ω 外部标准；
环境完整求值图未进入部分真值源公式。仍使用环境含 Collection 的 Core，
并非 Z₂ 的 BM4 良序终局，也不是两个层间有限稳定性已完成。
验证：默认构建 2302 jobs，原终局、有限层79、三阶3009／62出口、
全桥8501声明审计通过，仅三项标准公理。450旧警告与163冻结资源不变；
五项Lean文件两树哈希一致，差异/禁止项检查通过。日志 bms-truth-finite-*；
无遗留构建，未提交推送，未重跑根、二阶／BMSTools专门审计或远端CI。
普通额度剩余41%，≤40%立即停止。下一步将实际有限部分真值族用于
有限稳定对构造，需证明两个实际层查询一致，不能只用单层正确性替代。
BM4内部算法、任意下降实数对应和真正Z₂目标保持仍缺，目标active。

前一检查点：一般后继层匹配极性的双向正确性已经完成。新模块
PowerlessPartialTruthStep.quantifier_l 的反极性分支消费 Successor.promotion_l，
同极性保留严格子码归纳；complete_l 装配全部五类分类记录的真实内部
归纳；source_l 与 Successor.source_l 合成匹配分类极性的双向结论。
没有未填的推进条件；前驱正确性仍为外部递推假设，整个有限族未装配。
小层只需实际有限支持，环境仍需完整 PowerlessTheory（含 Collection）。
验证：默认构建 2299 jobs；原终局、有限层 79、三阶 2998／62 出口、
全桥 8490 声明审计通过，仅三项标准公理。450 旧警告和163冻结资源
不变，三项 Lean 文件两树哈希一致；差异与禁止项检查通过。
日志 bms-successor-step-*，无遗留构建，未提交推送，未重跑根、二阶／
BMSTools 专门审计或远端 CI。普通额度剩余42%，≤40%立即停止。
下一步：实际数码由 Natural.successor_exists_l 与 successor_mem_l 构造，
结合零层 source_l 和一般 Step.source_l 按外部 Nat 建有限正确性族；
实际高层用 TruthStage.exists_l 对各层 oracle_m(formula_m k) 的有限列表
实例化。不要将小层假设改为完整 Core。有限稳定对、BM4 内部算法、
下降实数对应与真正 Z₂ 目标保持仍未完成，目标 active。

前一检查点：实际层的一般后继低层调用已完成。新模块
PowerlessPartialTruthSuccessor 的 lower_sound_l 用内部后继单射性识别
实际前驱，分类/有限赋值绝对性及前驱匹配极性双向正确性证明可靠性。
lower_complete_l 把指定前驱分类送进真实有限支持证书；promotion_l
由 a∈succ(m) 推出 a⊆m，经分类单调性处理任意严格降层，不再限制≤1。
source_l 沿原 Oracle 接受证书给出整个后继接受可靠性。这四项仍消费
前驱层匹配极性正确性作为递推假设，整个有限层递推尚未装配。
验证：默认构建 2298 jobs，原终局、有限层 79、三阶 2995／62 出口、
全桥 8487 声明审计通过，仅三项标准公理。450 原警告不变，163 冻结
资源不变，三项 Lean 文件两树哈希相同；差异/禁止项检查通过。
日志 bms-successor-stage-*；无遗留构建，未提交推送，未重跑根、二阶／
BMSTools 专门审计或远端 CI。普通额度剩余 42%，≤40%立即停止。
下一步：推广 Progress.quantifier_l，反极性分支消费新 promotion_l；
仿 First.complete_l 装配全部五类规则，再合并新 source_l 为一般后继
匹配极性双向正确性。最后按外部 Nat 装配实际 numeral 与有限支持族。
有限稳定对、内部 BM4 算法、下降实数、Z₂ 目标保持仍缺；目标 active。

前一检查点：一般后继的有限支持证书引入已接通。Introduction 新增
oracle_formula_l（原低层矩阵参数语义）、lower_l（真实低层调用进入
接受）、successor_l（前驱匹配极性的双向正确性产生后继两种标记）。
小结构只需实际 OracleIntroduction 有限支持，不要求完整 Core；
successor_l 的前层正确性尚须由一般有限层递推提供，不能当作该递推完成。
默认构建 2297 jobs，原终局、有限层 79、三阶 2991／62 出口及全桥
8483 声明审计通过，仅三项标准公理。450 条原警告完全不变，163 冻结
资源不变，两项修改的 Lean 文件两树哈希相同；差异及禁止项检查通过。
日志 bms-successor-introduction-*；无遗留构建，未提交推送，未重跑根、
二阶／BMSTools 专门审计或远端 CI。普通额度剩余 43%，≤40%立即停止。
下一步：用前驱唯一性、分类单调性和实际层分类绝对性消费 successor_l，
推广第一层专用的降层与量词分支；再完成一般外部有限层递推。
有限稳定对、内部 BM4 算法、下降实数与 Z₂ 目标保持仍缺；目标 active。

前一检查点：第一层部分真值已完成匹配分类极性的双向正确性。
OracleParameters 已覆盖 witness/无界存在/有界正负规则的无核心参数
语义，Introduction 对应规则产生实际证书。Progress.quantifier_l
同极性用严格子码归纳，反极性用严格降层；bounded_l 保留整个界集合、
非法槽及界槽无取值，更新图由实际内部有限图层内闭包取回。
PartialTruthFirst.complete_l 沿原内部代码归纳装配五类分类规则；
source_l 将实际 formula_m 1 与完整层求值双向连接，涵盖非标准内部码
和全部层内有限赋值。范围要求分类极性与接受标记匹配，不是任意极性
无条件完备，也不是 Z₂ 中的 BMS 良序终局。
TruthFirstStage.exists_l 在任意给定序数和 ω 之上构造具有上述性质的
真极限层，返回原六参数、实际赋值集合、环境完整求值图及有限支持模型；
不预设这样的层存在，不把完整求值图塞进源公式参数。
验证：默认构建 2297 jobs；原终局、有限层 79、三阶 2988／62 出口、
全桥 8480 声明审计通过，仅三项标准公理。七个本轮 Lean 文件两树
哈希一致，450 条旧警告文字及次数不变，163 冻结资源不变；禁止项
扫描和差异检查通过。日志 bms-partial-first-*；无遗留构建，未提交
推送，未重跑根工程、二阶／BMSTools 专门审计或远端 CI。
下一步推广一般后继层：先用前驱唯一性和分类单调性，把较低层分类
转到指定前驱，再消费前层匹配极性的双向正确性构造原 lower_m 调用。
通过当前有限支持进入 lift_m，不向小层传入完整 Core。已有与非和
有界推进适用于任意目标层；第一层专用 quantifier/promotion 需推广。
之后仍缺整个有限递推族、有限稳定对、BM4 内部算法、任意下降实数
对应及实际 Z₂ 目标保持。环境仍消费含 Collection 的完整 Core。
最后额度检查剩余 44%；用户要求普通额度剩余≤40%立即停止并汇报。
目标 active，不把第一层部分真值里程碑当作目标完成。

前一检查点：零层 source_l 已覆盖任意被忽略的内部层号参数。
PartialTruthIntroduction.bounded_l 用实际有限支持把全部内部有界真值
送入后继接受；promotion_l 对目标不超过 1 的严格降层分类还原 m = 0，
不使用同一码归纳。nand_l 允许两个子式各自提供证书；
PartialTruthProgress.boolean_l 已按真实分类记录证明子码严格变小，
并消费原内部归纳性质与完整层求值方程完成与非推进。
EvaluationParameters/TruthParameters/OracleParameters 保留原递归公式
和原接受公式，提供任意结构上的参数语义，不要求小层完整 Core。
展开瓶颈以分阶段处理解决：先用 lift/nand 的语义接口和
Term.eval_weakenBound，再展开环境取值；不提高默认步数上限。
验证：默认构建 2295 jobs；原终局、有限层 79、三阶 2953／62 出口、
全桥 8445 声明审计通过，只允许三项标准公理。九个本轮 Lean 文件
两树哈希匹配；450 条旧警告文字及次数不变，163 冻结资源不变；
禁止项扫描和差异检查通过。日志 bms-partial-boolean-*；无遗留构建。
未提交推送，未重跑根工程、二阶／BMSTools 专门审计或远端 CI。
下一步：为 witness/量词原规则证明无核心参数语义，再用现有有限图
层内闭包、更新绝对性和精确求值方程，完成有界量词与无界存在推进；
然后装配第一层完备性及整个外部有限递推。有限稳定对、BM4 内部算法、
下降实数对应和 Z₂ 目标保持仍未完成，环境仍消费含 Collection 的 Core。
本轮最后额度检查剩余 45%；用户要求剩余不超过 40% 时停止并报告。
目标仍 active，不把这些局部构造子结果当作 BMS 良序终局。

前一已验证检查点：OracleRules 已将全部局部接受构造写成原公式；
OracleIntroduction 从这些规则的真实 Hilbert 推导抽取有限 Core 支持。
TruthStage.exists_l 已把任意有限公式列表的这类支持与原 OracleSupport
一起装配进任意高的实际真极限层，不假设小层完整 Core。
RelativeParameters 允许域参数在小域之外，PartialTruthProperty 给出
原完备性正文、全部内部代码的归纳接口和已经证明的零层实例。
第一层的构造子推进条件仍未证明，不能将该归纳接口当作完备性。
验证：默认构建 2290 jobs；原终局、有限层 79、三阶 2901／62 出口、
全桥 8393 声明审计通过，只允许三项标准公理。七个本轮 Lean 文件
两树哈希匹配；450 条旧警告文字及次数不变，163 冻结资源不变；
禁止项扫描和差异检查通过。日志 bms-oracle-introduction-*；无遗留
构建，未提交推送，未重跑根工程、二阶／BMSTools 专门审计或云端 CI。
目标仍缺第一层及任意有限层的完整双向正确性、有限稳定对、BM4
内部算法、下降实数对应和 Z₂ 目标保持；环境仍用含 Collection 的 Core。
当前用户额度限制：普通额度剩余不超过 40% 时停止工作并报告恢复点。

前一检查点：PowerlessTruthIntroduction 抽出原有界真值进入接受证书
的实际有限核心支持。PowerlessPartialTruthZero.source_l 在真实层中
证明 formula_m 0 与有符号完整层求值双向对应，覆盖全部内部有界
代码和层内有限赋值，不假设小层完整 Core。PowerlessPartialTruthOne
的 lower_l/source_l 以此消去第一后继层的低层可靠性前提，取反分支
使用零层双向对应；第一层完备性仍未完成。
PowerlessTruthStage.exists_l 消费 ClassFiniteSupport，把求值支持、
零层引入支持和任意外部有限列表中全部 OracleSupport 合并，在任意
指定序数及 ω 之上构造实际真极限层。返回编码参数、环境完整求值图、
全部支持模型、各原收集／扩充闭句、零层双向正确性和第一层可靠性。
不是先假设层满足支持；也没有把完整求值图放入源公式参数。
验证：默认构建 2286 jobs；原终局、有限层 79、三阶 2845／62 出口、
全桥 8337 声明审计通过，只允许三项标准公理。六个本轮 Lean 文件
两树哈希匹配；450 条旧警告文字及次数不变，163 冻结资源不变；
禁止项扫描和差异检查通过。日志 bms-truth-stage-*（独立模块另有
bms-truth-introduction-module、bms-partial-truth-zero-module、
bms-partial-truth-one-module）。无遗留构建，未提交推送；未重跑根工程、
二阶／BMSTools 专门审计或远端 CI。
下一步按实际内部代码及 Lévy 分类证明第一层接受完备性，再推进
外部层号归纳。OracleSupport 目前给原收集／扩充闭句，不等于全部
构造闭包已在小层逐项接线；不得直接传入要求小层完整 Core 的
OracleClosure/OracleBounded 接口。环境仍需完整 Core（含 Collection）；
有限稳定对、BM4 内部算法、下降实数对应和 Z₂ 目标保持仍待完成。
目标保持 active，不将这些局部真值结果当作 BMS 良序终局。

前一检查点：PowerlessClassCore.models_l 已证明实际层次类满足完整
PowerlessTheory，包括任意 Project 分离和收集模式。SourceParameters
保留一／两个见证槽并打开其余参数；SourcePadding 加入七个实际自由
参数，ClassComprehension 接回任意原环境，ClassAxioms 验证六类基本公理。
ClassFiniteSupport.models_l 进一步对任意有限核心闭句列表，在任意
指定序数之上构造满足它的真极限层，返回既有 MemberStructure，
不预设稳定对或小层满足性。以上仍假设环境完整 Core（含 Collection），
不能传入仅满足弱集合理论的 SecondOrderTMC.models_l。
验证：默认构建 2282 jobs；原终局、有限层 79、三阶 2824／62 出口、
全桥 8316 声明审计通过，只允许三项标准公理。九个本轮 Lean 文件
两树哈希一致；450 条警告文字及次数不变，163 冻结资源不变；差异／
禁止项检查通过。日志 bms-class-core-*，无遗留构建，未提交推送。
未重跑根工程、二阶／BMSTools 专门审计或远端 CI。
下一步用 OracleSupport.support_m B 的 sentences 和 subset 取得实际
层模型，并在部分真值消费者中使用 models_l；不能只增加空的转发接口。
仍缺完整部分真值双向正确性、有限稳定对、BM4 内部算术及目标保持的
Z₂ 转译。目标继续 active；本检查点不是 Z₂ 终局。

前一检查点：ClassSeparation 在真实反射层后继中构造相对化原公式
所定义的子集，并证明其属于层次类；ClassCollection 构造一个类内
收集集，覆盖全部有类内见证的输入（允许部分定义）。ClassBasic
补齐共同层、传递性、层本身／全部序数／ω/e/T/标签归属、空／对／并闭包。
HierarchyClass.lift_env_l 证明环境提升左逆。类结构与旧成员结构的
关系解释逐点一致，通过 relation_l 仅改关系字段；未修改旧结构定义。
默认构建 2276，原终局／有限层 79／三阶 2784、62 出口／全桥 8276
审计通过。六个本轮 Lean 文件两树匹配；450 条警告文字、次数与旧版
相同，163 冻结资源不变，禁止项／差异通过。日志 bms-class-closure-*。
无遗留构建，未重跑根工程、二阶／BMSTools 专门审计及远端 CI，未推送。
下一步装配真实类模型的全部 Project 模式，不能把当前存在性构造
误报为 Models Core。先用 fo_formula 进入原 AST，再在 Opening.binding_m
上 liftBound 一／两次保留见证槽、只打开参数槽，加入实际六个编码参数
（其类内性已由 ClassBasic.parameters_l 证明）。连续 abstractFreeTop
两次会反转两个槽，须避免错接。完整有限支持、部分真值、稳定对、
BM4 内部算术及目标保持的 Z₂ 转译仍待完成；当前均依赖完整环境 Core。

前一检查点：SourceOpening／SourceRequests／SourceReflection 已完成
绑定到有限自由输入、实际存在及全称反例请求抽取、逐公式双向反射准则，
并构造严格更高的真极限反射层。parameters_l 先将全部类内自由参数
放入同一层；exists_l 返回参数包含性和反射，不假定稳定对或类满足核心。
存在性仍消费完整 PowerlessTheory，不是对象 Z₂ 终局。下一步是实际
类的分离／收集及有限支持、部分真值正确性与有限稳定对，再完成
BM4 内部算术程序、任意下降实数对应和目标保持的 Z₂ 转译。
验证：默认构建 2273；原终局、有限层 79、三阶 2766／62、全桥 8258
审计通过。五个本轮 Lean 文件两树哈希一致；450 条旧警告的文字和
次数相同，163 个冻结资源不变，差异／禁止项检查通过。日志
bms-source-reflection-*。全桥审计入口实际在工作区 outputs 下，须用
绝对路径，不是 SHORT/ConstructibleBridge/outputs。无遗留构建，未推送。
未重跑根工程、二阶／BMSTools 专门审计或远端 CI。目标保持 active。
以下为累计历史进展；遇到旧“尚未反射”或停止指令时以上述状态为准。

用户在发布 BMSTools 后要求开始尝试固定 n 的 Z₂ 证明。最新研究入口为
FIXED_HEIGHT_Z2.md 和 FiniteHeight.lean；目标覆盖当前高度 ≤ n 的全部
生成数组，而非只覆盖 n 行种子的后继。已完成有界载体与有限高度纤维的
良基性／无限下降等价。FiniteHeightRepresentation 进一步以最小有限
稳定边界为前提直接表示全部低高度合法数组，并推出受限一步良基性；
仍未完成对象 Z₂ 推导。此解法绕过种子覆盖，不调用先要求 Acc 的可比性。
PowerlessFiniteChain 已独立编译：对实际内部自然数归纳构造有限链，
不假定内部自然数标准；调用者仍须证明延长条件与所用背景公理。
PowerlessGlobalBoundary 已证明从已有稳定对取全局最小下端点及内部
层号截断；保留原 κ 有界接口不变。最新构建 2251 jobs，三阶审计
2422／全桥 7914，通过。尚缺稳定对存在、反射实例和目标的 Z₂ 推导。
最新增量：PowerlessTruthClosure 已完成原检查式的值语义、集合族并、
父记录添入、有界初始接受及实际证书收集；PowerlessTruthClosureSupport
从真实 Hilbert 推导抽取证书收集闭句的有限核心列表。完整构建 2253，
原终局／有限层／三阶 2467／全桥 7959 审计通过，旧 450 条警告不变。
小层满足有限支持仍待证明。旧 step_m 的无界存在分支只允许真极性，
不能把其 accepts_m 的任意层、任意极性完备性当作下一步的可行目标；
必须按外部固定层号构造部分真值并核验实际分类。目标保持未完成。

发布基点 4dde78b 已推送至 GitHub main；本轮新增证明尚未提交推送。

最新局部推进：PowerlessPartialTruth 给出外部固定层号的原公式族，已证明
零层接受构造与低层调用进入后继公式。PowerlessTruthOracle 的可靠性仍
保留低层公式可靠性前提。PowerlessOracleClosure / PowerlessOracleBounded
已完成实际证书并、添入、收集，以及与非、正无界存在、有界正负规则的
接受构造；有界负分支按实际集合收集，不假定界有限。
PowerlessOracleSupport 给出每个低层公式的收集／添入闭句的真实有限
Hilbert 支持，有限支持模型可直接使用原闭句。最新完整构建 2259 jobs，
原终局／有限层 79／三阶 2558／全桥 8050 审计通过；450 条警告不变，
八个本轮 Lean 文件两树哈希一致，163 个冻结资源不变。日志前缀为
outputs/bms-oracle-support-*，详细验收范围见 FIXED_HEIGHT_Z2.md。
下一步仍是指定小层满足有限支持、实际分类下的逐层双向真值正确性、
有限稳定对存在和最终 Z₂ 推导；不得以公式族或局部闭包替代终局。

最新见证闭包增量：五个模块完成部分收集、序数上界／最小化、固定二元
原公式的见证层选择、实际内部 ω 递归及极限闭包层。序列存在性仍要求
完整 PowerlessTheory 与显式层次覆盖；不是 Z₂ 定理或全公式初等性。
默认构建 2264 jobs；命名修正后聚合目标 2258 jobs，原终局／有限层 79／
三阶 2607／全桥 8099 审计通过。450 条历史警告不变，七个本轮 Lean
文件两树哈希一致，163 个冻结资源不变。日志 bms-source-witness-final-*。
无遗留构建，未推送。下一步检验限制见证到层次对象以消去全局覆盖，
再做有限支持反射；不能循环调用先要求稳定对的 models_l。目标仍在进行。

覆盖前提的新进展：Bound／Step／Sequence 的覆盖只要求指定公式的
见证落入层次，已同步所有调用点。PowerlessSourceWitnessDomain 给出
实际域公式及限制公式，并从完整 PowerlessTheory 构造限制见证的闭包层，
不再要求全宇宙覆盖。它没有证明类相对化的全部公式语义对应、有限反射
或 Z₂ 终局。接着做原公式的类相对化、有限参数请求编码及子公式反射；
不能从 Collection 直接假定一般反射。完整默认构建 2265 jobs；原终局、
有限层 79、三阶 2616／62、全桥 8108 审计通过。450 条历史警告不变，
六个本轮 Lean 文件两树哈希一致，163 个冻结资源不变。日志
bms-source-domain-*；无遗留构建，未推送。详情与原文线索见 FIXED_HEIGHT_Z2.md。

原公式类相对化已新增 PowerlessSourceClass：实际非空类子类型结构、
环境包含及绑定更新、原一元域公式代入、全十一构造子的量词限制，
以及 formula_l 的逐公式语义对应。此通用语义定理不假定类满足核心
或已有初等性；实际层次域的接入、有限参数打包与有限反射仍待完成。
打包已有 ordered_l／ordered_eq_l 可用，不应重新假定参数码存在。
验证：默认构建 2266 jobs；原终局、有限层 79、三阶 2642／62、全桥
8134 审计通过，450 条旧警告、163 个冻结资源不变，三个本轮 Lean
文件两树哈希一致，差异／禁止项检查通过。日志 bms-source-class-*；
无遗留构建，未推送，目标仍在进行。

新接线已完成：PowerlessHierarchyClass 对实际层次类证明非空、域公式
解释、类内环境提升与原公式相对化语义，消去通用接口的任意域解释前提。
PowerlessSourcePack 用实际有序对合并两个输入，证明准确编码／解码和
见证闭包传输，并构造对两个输入关闭层次内见证的更高极限层。
下一步：用既有 Values ℳ.Carrier (List.replicate n .set) 推进任意外部
有限元数，再组合有限子公式请求并证明反射；这两部分尚未完成。
验证：默认构建 2268 jobs；原终局、有限层 79、三阶 2666／62、全桥
8158 审计通过。450 条历史警告、163 个冻结资源不变；四个本轮 Lean
文件两树哈希一致，差异及禁止项扫描通过。日志 bms-source-pack-*，
无遗留构建，未推送，目标保持进行。

任意有限元数与共同闭包已新增 SourceTuple／SourceFamily：前者复用
Values 值列并处理零输入，证明实际请求码存在和真值对应；后者使用
两个互异标签合并有限列表，允许每条原公式有不同元数，返回同一个
真极限层对所有请求的见证闭包。没有标签／请求码存在的未证前提。
下一步是实际子公式抽取、绑定到自由输入的原替换与环境对应，再做
子公式归纳得到有限反射；目前尚未完成反射，更未完成 Z₂ 终局。
验证：默认构建 2270 jobs；原终局、有限层 79、三阶 2719／62、全桥
8211 审计通过。450 条旧警告内容和次数相同、输出顺序变化；163 个
冻结资源不变，四个本轮 Lean 文件两树哈希一致，差异／禁止项通过。
日志 bms-source-family-*，无遗留构建，未推送，目标保持进行。

## 当前任务：提取通用工具子库（2026-09-14）

用户给出两种收尾方式，本轮选择可复用工具抽取。推荐入口改为 BMSTools
及其四个分组，说明见 BMS_TOOLS.md。原实现和原 ZFC／可构造证明不搬动，
不再以继续闭合弱背景终局为本轮验收目标。下文检查点为历史记录。

## 最新：半小时限时增量完成后停止（2026-09-14）

用户仅授权先完成半小时内能闭合的部分，没有恢复无期限目标。
本次完成 PowerlessTruthMonotone 的 5 个定理，以及
PowerlessTruthCertificateUnion.union_l：给定真实二元并集，
两份证书的检查条件在并集中保持。没有增加任何背景公理。

最新检查点 third-order-truth-monotone，全门会话 25276 exit 0：
桥 2241 jobs；原终局及有限 63／二阶 2845／全桥 7884／三阶
2407 个声明审计通过，仅三项标准公理。两模块净增 6 个声明，
全部为定理；485 个 Lean 文件两树哈希一致，450 条旧警告不变，
163 个冻结资源不变，差异／禁止项与 62 个无规模界出口通过。
无遗留构建；根与远端 CI 未重跑，未提交推送。

下一未证项：父记录添入、任意集合族合并、子证书族在当前层
内的实际收集和有限支撑、固定层接受完备性。二元并集保持
不等于这些义务已完成。详见背景第 58 节。限时工作完成后
继续保持停止，等待用户下一指令，不自动续作完整证明。

## 2026-09-14 最新指令：停止与快速收尾

此项覆盖下文的恢复／继续说明。用户要求停止全部当前任务，
评估完整 Z₃ 背景路线余量；超过 5 小时则快速收尾。
本次已核对：无活动目标、无运行中的子代理、无 Lake/Lean/
Leanchecker 进程。刚被中断的继续轮只做读取和设计，没有
创建 PowerlessTruthMonotone.lean 或其他新 Lean 文件。

现封存在 third-order-truth-certificate 绿色检查点，只核对日志、
源码与冻结资源并更新交接；不再开发证明、不全量重编译、
不提交推送、不发布未完成的三阶证明版。再次启动须用户明确要求。
本次阶段性收尾不代表 BMS 降背景目标完成。

余量与最短重启路线见 THIRD_ORDER_BACKGROUND.md 第 57 节。
无新数学障碍时粗略预算为 50–120 小时有效工作量，不是交付保证；
现有证据不支持 5 小时内完成完整弱背景证明。

> 2026-09-13 恢复说明：用户已明确解除剩余 50% 停工限制，并要求继续向
> 强度明确受控的三阶子系统或其他标准背景推进。下文保留原停工检查点
> 作为历史记录；当前路线见 `THIRD_ORDER_BACKGROUND.md`，两版保护要求
> 见 `PROOF_VARIANTS.md`，最新实际验收见 `FINITE_BOUNDARY_VERIFICATION.md`。

## 恢复后的当前断点

最近检查点为 `third-order-truth-certificate`（2026-09-14）：桥
2239 jobs、原终局通过；有限层 63／二阶 2845／全桥 7878／三阶
2401 个声明通过，仅三项标准公理。最终全门会话 61946 exit 0，
483 个 Lean 文件两树哈希一致，450 条旧警告逐条不变，163 个
冻结资源未变；差异与禁止项通过，60 个无规模界出口通过。
无遗留 Lake/Lean；未重跑根或远端 CI，未提交推送。

五个新模块、22 个公开声明（11 个定理）完成真实更新见证、
有界正／负分支、真值基例、同一局部规则及整表证书。
PowerlessTruthCertificate.certificate_m/accepts_m 不含 U、δ 或 H；
每个成员必须解析为记录且原代码属于内部 ω。sound_l 沿原
Formula 内部码归纳证明整表可靠，accepts_source_l 消去子记录
可靠性前提并给同码同赋值查询。仍保留实际 proper 极限层和
小层求值有限片段条件；并非真值全部有证书。详见背景第 56 节。

下一步先证局部规则的记录集单调性、certificate_m 的实际添入／
并集闭包，不能仅引用 TruthSet 的 valid_l 保持。再使用不含 H
的证书关系收集有界负分支子证书族，过滤无关族成员并证明族
落在 U。当前求值有限片段不自动提供新 Collection／归纳实例，
须抽取并反射实际有限支撑，不能假定小层完整核心。随后完成
Σ₁ 正真／Π₁ 负假完备性、严格低层提升和固定层后继预算。

BM4 完整有限反射、任意下降实数与对象终局、标准解释、
精确强度及双版仍未完成。原语法、背景定义和冻结资源保持；
无规模界依赖及三项 Lean 公理不是强度校准。

前一检查点为 `third-order-truth-record`（2026-09-14）：桥 2234
jobs、原终局通过；有限层 63／二阶 2845／全桥 7836／三阶 2359
个声明通过，仅三项标准公理。最终全门会话 53885 exit 0，478 个
Lean 文件两树哈希一致，450 条旧警告逐条不变，163 个冻结资源
未变；差异和禁止项通过，56 个无规模界出口通过。无遗留
Lake/Lean，未重跑根或远端 CI，未提交推送。

六个新模块、38 个公开声明（27 个定理）完成实际真值记录、
坐标落级和原公式绝对性、真值标记、记录添入和集合族合并，
并把与非／正存在量词的记录规则接到原求值器。两个 source_l
最终只要求较小公式码 d∈c 的子记录可靠，原构造子 bounds_l
给码下降，未循环假定全表可靠。valid_l/valid_m 是含 H 的语义
后置性质，绝不能当作不含 H 的证书检查器。

表示计划已修正：有界量词的界未必有限；逐赋值有限行列表不能
直接承担集合多个分支。本轮采用集合记录容器，下一步以内部
码下降控制推理深度。尚未定义完整局部证书或证明其总可靠性。
先补有界量词假分支、实际收集分支族并证明其落级，再完成
基例／与非／正量词／有界分支／严格低层提升的局部证书及
可靠性、完备性、后继预算。详见背景文档第 55 节的具体断点。

BM4 完整有限反射、任意下降实数与对象终局、标准解释、
精确强度和双版本仍未完成。不要回退到旧 FOFormula，
也不要以三项 Lean 公理或无规模界依赖替代强度校准。

前一检查点为 `third-order-ambient-existential`（2026-09-14）：桥
2228 jobs、原终局通过；有限层 63／二阶 2845／全桥 7778／三阶
2301 个声明通过，仅三项标准公理。全门会话 78248 exit 0，472
个 Lean 文件两树哈希一致，450 条旧警告逐条不变，163 个冻结
资源未变；差异和禁止项通过。53 个无规模界出口，不是强度校准。
无遗留 Lake/Lean，未重跑根或远端 CI，未提交推送。

五个新模块、18 个公开声明（12 个定理）完成量词组合规则及原
有界正文的实际存在量词真值。先证明真实函数图更新保持定义域，
再以域内量化的长度和值域表达有限赋值、合法槽位；量词公式同时
量化见证 a 和真实更新图 g。原 Formula 正文已用上一检查点的
有界 truth_m 实际填入，ThirdOrderAmbientExistential.source_l
接入 Cκ 原零层证书。最终查询比较不预设 f 或变量槽位合法，
公式 guard 与原求值器一致；U／δ／完整 H 不是源公式参数。

下一步仍是有符号有限轨迹、与非和正量词的同层闭包、严格低层
提升、固定层分类器的可靠性／完备性及后继预算。不要把一个
存在构造子的实例冒充全 Σ₁ 分类器，也不导入旧 FOFormula。
之后还须接 BM4 完整有限反射（含上端点稳定边）、任意下降实数
与对象终局、标准解释／精确强度／双版。详见背景文档第 54 节。

更早检查点为 `third-order-bounded-truth`（2026-09-14）：桥 2223
jobs、原终局通过；有限层 63／二阶 2845／全桥 7751／三阶 2274
个声明通过，仅三项标准公理。全门会话 90870 exit 0，467 个 Lean
文件哈希一致，450 条旧警告逐条不变，163 个冻结资源未变；差异、
禁止项通过。51 个无规模界出口，不是强度校准。无遗留 Lake/Lean，
未重跑根或远端 CI，未提交推送。

四个新模块、11 个公开声明（7 个定理）完成有界当前域真值基例。
truth_m 的参数不含当前域 U／高度 δ／完整求值图 H；实际早传递层
及求值有限片段给证书见证，原有界证书正确性给同码同赋值比较。
ThirdOrderBoundedTruth.source_l 接入 Cκ 原零层证书的任意合法极性。
公式本身未分类为 Δ₀，不是所有内部层号的统一真谓词。

下一步：用原 Formula 构造有符号有限轨迹及正层当前域真值，
处理 NAND、量词、严格低层提升与后继预算，再接 BM4 有限反射。
量词更新仍须保留实际 map 条件，update_m 只比较取值，不能排除
图中的额外非有序对元素。旧 TextbookAmbientTruthClassifierFormula
只作数学参考，不导入其 FOFormula。任意下降实数与对象终局、
标准解释、精确强度和双版本仍未完成。详见背景文档第 53 节。

更早检查点为 `third-order-finite-stability`（2026-09-14）：桥 2219
jobs、原终局通过；有限层 63／二阶 2845／全桥 7729／三阶 2252
个声明审计通过，仅三项标准公理。全门会话 95625 exit 0，463 个
Lean 文件两树哈希一致，450 条旧警告逐条不变，163 个冻结资源
未变，差异和禁止项通过。49 个指定出口无规模界依赖，不是强度
校准。无遗留 Lake/Lean，未重跑根或远端 CI，未提交推送。

三个新模块、四个公开定理完成原 limit/proper/stable 源公式的
有限片段解释。stable_m 六个系统见证完整取回，查询保持 A、G、F
原顺序；不调用小层完整核心。统一预算先于早层、原环境和待比较
的内部层号选择，有限模型性与编码参数由已有构造实际给出。

该检查点当时的下一步：BM4 复杂度重编号和完整有限反射，特别是指向当前上端点
的稳定边。两具名层公式绝对性不能把 κ 当作 Cκ 内参数，也不能
代替对整个当前域的真值比较。旧 EffectiveStability 的 FOFormula
只供数学结构参考，新路线继续使用原 Formula。其后仍需任意环境
下降实数、对象终局、标准解释及精确强度，不能发布第二份完整
良序证明。详见背景文档第 52 节。

前一检查点为 `third-order-finite-hierarchy`（2026-09-14）：桥构建
2216 jobs，原终局审计通过；有限层 63／独立二阶 2845／全桥 7722／
独立三阶 2245 个声明通过，仅三项标准公理。串行全门会话 59924
返回 exit 0；460 个 Lean 文件两树哈希一致，450 条旧警告逐条不变，
163 个冻结资源未变，差异和禁止项检查通过。47 个指定出口未引用
规模界接口，不是强度校准。无遗留 Lake/Lean，未重跑根工程或
远端 CI，未提交或推送。日志为 `bms-third-order-finite-hierarchy-*`。

七个新模块、28 个公开声明（21 个公开定理）完成原累计步骤、递归、
hierarchy_m、stage_m、system_m 的有限片段源解释，保留原语法和
量词。原层次存在闭句已有实际 Hilbert 有限支持，整个递归图由环境
唯一性取回；内部指标不限标准或有限序数。统一反射预算先于早层
端点选择，原 stable_n(α,κ) 下，所有 β∈α 的层值、完整赋值集和
求值图都属于 Cα。不假定 Core(Cα)，不取消原稳定条件。

该检查点当时的下一步：原 stable_m 的有限片段解释，再接 BM4 重编号、完整有限
反射、任意下降实数与对象终局，最后做标准类型化解释和精确强度。
不能直接调用需 Core(U) 的旧稳定公式表示。当前完整理论含 P(ω)
作为集合存在，不能与纯无幂集核心混称为等一致 Z₂；有限支持的精确
强度也尚未校准。仍不可发布第二份完整良序证明。详见背景文档第 51 节。

前一检查点为 `third-order-finite-operator`（2026-09-14）：桥构建
2209 jobs，原终局审计通过；有限层 63／独立二阶 2845／全桥 7672／
独立三阶 2195 个声明通过，仅三项标准公理。串行全门会话 29889
返回 exit 0；453 个 Lean 文件两树哈希一致，450 条旧警告逐条不变，
163 个冻结资源未变，差异和禁止项检查通过。43 个指定出口未引用
规模界接口，不是强度校准。无遗留 Lake/Lean，未重跑根工程或
远端 CI，未提交或推送。日志为 `bms-third-order-finite-operator-*`。

本轮七个模块、59 个公开声明（36 个公开定理）已完成原切片、任意
前史、隶属关系图和完整算子存在的有限支持，以及实际早层中的闭包。
`PowerlessFiniteStageOperator.source_l` 保留原两个存在量词，
只要求早层满足固定有限理论；`ThirdOrderFiniteStageOperator`
从实际 Core(Cκ) 反射出该有限片段，预算先于早层端点选定，继而
证明所有 B∈Cα 的原 D(B)∈Cα。未假定所有 proper 层有核心。

该检查点当时的下一步：原 step_m 的有限片段绝对性 → 原递归与 hierarchy_m 的
源解释（本轮关系图、任意前史闭包已可使用）→ 层次存在闭句的有限
支持及整图成员性 → stage/system/stable。不能再把 Core(U)
作为隐含前提。之后接 BM4 重编号、完整有限反射、任意下降实数与
对象终局，再做标准类型化解释和精确强度；当前仍不可发布第二份
完整良序证明。源码接口与证据详见背景文档第 49–50 节。

前一检查点 `third-order-finite-core` 已通过全门，会话 82341 exit 0：
桥 2202／全桥 7585／三阶 2108；八个模块、45 个公开声明（29 个
公开定理），446 个 Lean 文件哈希一致，39 个无规模界出口。
原签名强完备性、Formula 相对化、实际 Hilbert 有限支持及早层
完整赋值/求值闭包已完成。支持由非计算选择取得，不是可执行的
数值预算或 PRA 验证的证明生成器。


更早检查点为 `third-order-core-stage`（2026-09-14）：桥构建 2194 jobs，
原终局审计通过，有限层 63、独立二阶 2845、全桥 7512、独立三阶
2035 个声明通过，仅三项标准公理。438 个 Lean 文件两树哈希一致，
450 条旧警告逐条不变，163 个冻结资源未变；差异及禁止项检查通过。
36 个指定出口无规模界常量依赖，不是强度校准。串行全门会话 7275
返回 exit 0，无遗留 Lake/Lean 进程；根工程未重跑，未提交或推送。

七个 `PowerlessCoreStage*` 模块新增 31 个公开定理：对实际 proper
极限层 U=Cδ，显式给定 Core(U) 后，完整赋值集、求值图、切片、
算子、前史、累计步骤、层次图、单层、系统及原稳定公式的成员性／
内外一致均已证明。原源 Formula 和参数槽未改。五个 Cκ 专用模块
改为以已证 `ThirdOrderStageCore.models_l` 实例化通用结论，保留
19 个原接口；改写前后 Lean 类型指纹逐项相同。详见第 48 节。

下一步必须消去早层显式 Core 前提中超出有限反射能力的部分，而非
假定所有 proper Cδ 满足 Core。候选是为固定源存在／唯一及解释
结论提取原语言的有限理论支持，再反射这些有限条件。上游
`Completeness/ProofTheoryCore.lean` 有 Hilbert 推导的有限支持，
但本轮仅核对其签名，尚未构造所需对象推导、相对化或有限片段。
不能把 Lean 公理依赖扫描当作对象有限支持。之后仍须完成 BM4
层号重编号和有限反射合同、任意环境下降实数、对象终局、标准
类型化解释及精确强度；目前不可发布第二份完整良序证明。

前一检查点为 `third-order-certificate-absolute`（2026-09-14）：桥构建
2187 jobs，原终局审计通过，有限层 63、独立二阶 2845、全桥 7481、
独立三阶 2004 个声明通过，仅三项标准公理。431 个 Lean 文件两树
哈希一致，450 条旧警告逐条不变，163 个冻结资源未变；差异及禁止项
检查通过。34 个指定出口无规模界常量依赖，不是强度校准。串行全门
会话 59700 返回 exit 0，无遗留 Lake/Lean 进程。根工程未重跑，
未提交、未推送、未运行远端 CI。

九个模块新增 30 个公开定理，含编译辅助声明审计净增 31。内部自然数
归纳给 D⊆N、N∈ω 的实际有限子集成员性；原有界证书、Lévy 记录、
全部生成规则和分类证书已双向对应。全部有限赋值上的查询一致性及
分层一致关系已双向对应，最终接回原 stable_l/stable_m 的六个系统
见证。出口为 `ThirdOrderStageStability.stable_l` / `source_l`；
实际 U=Cκ，不假定内 Core，不改原公式，未作 BM4 复杂度重编号。
详见 THIRD_ORDER_BACKGROUND 第 47 节。

该检查点提出先核对 BM4 反射合同所需的早层范围：当时只证明 Cκ 中的
stable_m 绝对性，不能推给每个 proper 极限层。补足所需早层的有限
理论和层次图闭包后，再用原 Formula 的源反射预算接内部重编号。
旧 EffectiveStabilityComplexity 使用 Constructible 的 FOFormula，
不能导入独立三阶证明。任意环境下降实数、对象终局及标准类型化解释／
精确强度仍待完成，尚不可发布第二份完整证明。

更早检查点为 `third-order-hierarchy-absolute`（2026-09-14）：桥构建
2178 jobs，原终局审计通过，有限层 63、独立二阶 2845、全桥 7450、
独立三阶 1973 个声明通过，仅三项标准公理。422 个 Lean 文件两树
哈希一致，450 条旧警告逐条不变，163 个冻结资源未变，差异及禁止项
检查通过。31 个指定出口无规模界常量依赖；这不是强度校准。
串行全门会话 61495 返回 exit 0，无遗留 Lake/Lean 进程。根工程
未重跑，未提交、未推送、未运行远端 CI。

四个模块新增 14 个实际导出的公开定理，审计净增 14 个声明。
原累计步骤、整个 hierarchy_l、单层 stage_l 和 system_l 的内外
语义已对应；原 hierarchy_m、stage_m、system_m 在任意项环境中
正确解释，编码参数对应保持显式。对域内序数 α 的实际层次图
已证明 f∈Cκ，对 α∈κ 的系统取得 A/S/F∈Cκ。步骤输出取回用
D 闭包，递归反向用二次并作统一值域界及一般前史闭包；内部存在性
只有在内外一致后才通过环境唯一性给整图成员性。详见第 46 节。
所有 proper 早级的 Core、原分层 stable 公式及 BM4 终局不在本轮结论中。

前一检查点为 `third-order-stage-core`（2026-09-14）：桥构建 2174 jobs，
原终局审计通过，有限层 63、独立二阶 2845、全桥 7436、独立三阶 1959
个声明通过，仅三项标准公理。418 个 Lean 文件两树哈希一致，450 条
旧警告逐条不变，163 个冻结资源未变，差异及禁止项检查通过。
25 个指定出口无规模界常量依赖；这不是一致性强度校准。根工程未重跑，
未提交、未推送、未运行远端 CI；串行全门会话 59470 返回 exit 0。

七个模块新增 23 个公开声明（1 定义、22 定理），含编译辅助净增 40 个。
已从共尾原源初等性实际证明 Cκ 满足完整 PowerlessTheory：任意有限
参数环境先放入一个 proper 初等早级，分离经源覆盖取得子集；收集
以同一早级作为实际集合界。基础公理及原 Project 公理模式均已接回，
没有假定 Core(Cκ)。进一步对任意 f/a∈Cκ 构造严格前史 H∈Cκ，
对任意 A∈Cκ 构造原隶属关系图 R∈Cκ，不限于内部自然数。
原递归公式的关系见证条件已经消去，但其结论仍是同一小结构中的
语法/语义桥，不是任意递归正文的跨结构绝对性。详见第 45 节。

前一检查点为 `third-order-slice-family`（2026-09-14）：桥构建 2167 jobs，
原终局审计通过，有限层 63、独立二阶 2845、全桥 7396、独立三阶 1919
个声明通过，仅三项标准公理。411 个改动或新增 Lean 文件两树哈希一致，
450 条旧警告逐条不变，163 个冻结资源未变，差异及禁止项检查通过。
18 个指定出口无规模界常量依赖；这不是一致性强度校准。根工程未重跑，
未提交、未推送、未运行远端 CI。

最新九个模块新增 20 个公开定理，全部实际导出，含编译辅助净增 25 个
被审计声明。原追加图、point/slice、family 公式绝对性已闭合；查询的
正见证沿 F 成员链取回追加图。实际切片先统一落在一个后继早级 J，
再将 J 作为元素升至更高极限层，源覆盖给整个切片族属于 Cκ。
ThirdOrderStageEvaluationOperator 对 A∈U=Cκ 实际构造 D(A)∈U，
并在任意项环境、编码参数取值对应时证明原 operator_m 正确解释。
S/F 的存在量词由此前已证成员性处理，没有假定小结构核心或更换原模板。
九个模块均已同步并通过完整审计；见 THIRD_ORDER_BACKGROUND 第 44 节。

前一检查点为 `third-order-evaluation-member`：桥构建 2158 jobs，
原终局审计通过，有限层 63、独立二阶 2845、全桥 7371、独立三阶 1894
个声明通过，仅三项标准公理。402 个改动或新增 Lean 文件两树哈希一致，
450 条旧警告逐条不变，163 个冻结资源未变，差异及禁止项检查通过。
14 个指定出口无规模界常量依赖；这不是一致性强度校准。根工程未重跑，
未提交、未推送、未运行远端 CI。

最新八个模块有 22 个实际导出的公开声明（4 定义、18 定理），审计含
编译辅助净增 51 个声明。已对 A∈U=Cκ 构造实际赋值集合 S 和原求值图 F，
并证明 S∈U、F∈U。有限前缀沿原递归正文构造、限制并证明与 F 同值；
其原 Formula 在实际 proper 极限层正确解释，不假定小结构核心。
不含 F 的逐点成员公式经源覆盖给 F∈D(Cβ)，再传入 Cκ。
不能以 A=U 代入 A∈U，也不宣称求值子集族、无限层次或 BM4 终局已闭合。
详见 THIRD_ORDER_BACKGROUND 第 43 节；八个模块均已同步并通过完整审计。

前一检查点为 `third-order-evaluation-range`：桥构建 2150 jobs，
有限层 63、独立二阶 2845、全桥 7320、独立三阶 1843 个声明通过，
仅三项标准公理；394 个改动或新增 Lean 文件两树哈希一致，450 条旧
警告逐条不变，163 个冻结资源未变。12 个指定出口的类型及正文依赖
不引用全集规模界。原终局审计通过；根工程未重跑，远端未改。

最新七个模块新增 15 个公开定理，计入编译辅助共净增 17 个被审计声明。
对 A∈U=Cκ，已证明全部有限 A 赋值 S∈U；对 A/S/H/n∈U 的原求值步，
输出 Y∈U。实际 evaluation_l 的全部内部编号取值及有限前史也属于 U，
并得到 F⊆U。进一步由精确值域的内部可数性取共同早级，再将该早级
和参数放入更高 proper 极限 Cβ（β∈κ），取得 A/S∈Cβ、F:ω→Cβ、
F⊆Cβ 及全部内部自然数前史 H∈Cβ。此处 F 仍未作为元素落级。
不能以 A=U 代入 A∈U 的接口。所有七个模块已同步、实际导出并全门通过。

前一检查点为 `third-order-evaluation-source`：桥构建 2143 jobs，
有限层 63、独立二阶 2845、全桥 7303、独立三阶 1826 个声明通过，仅三项
标准公理；387 个改动或新增 Lean 文件同步，450 条旧警告逐条未变，
163 个旧资源哈希未变。原终局公理审计同时通过，根工程未重跑、远端未改。

该检查点六个模块、25 个实际导出的公开声明（4 定义、21 定理）完成：
原自然数隶属关系 R 的极限层成员性；不假定小结构核心的原 relation/
history/recursion 桥；任意项环境中原 evaluation_m 的实际极限层
正确解释；A∈Cα（ω∈α，α 为极限）的全部有限赋值集合 S∈Cα+1。
完整审计净增 56 个声明，含编译辅助声明。R 存在前提已消去，相关
有序对闭包由域内 R 推出；不要重新暴露成重复前提。S 的结论确实
在后继层，不能改写为 S∈Cα。见 THIRD_ORDER_BACKGROUND 第 41 节。
本轮六个文件全部同步并通过完整审计，没有待编译的本轮 Lean 草稿。

前一检查点六个模块、21 个实际导出的公开定理完成原 node/constructor、更新、
query/equal/member、exists/clause、原 step_m、序数前史及原递归语义
evaluation_l 的绝对性。实际 proper 极限层出口消去所需闭包条件。
二次并提供域内统一值域；有限前史的图由内部有限图闭包取回。
见 THIRD_ORDER_BACKGROUND 第 40 节。所有六个文件在主树和短树均已
同步并通过完整审计，没有待同步或未编译的本轮 Lean 草稿。

首次完整审计发现 update_source_l 未导出，将其提前至 member_l 前并用
显式证明块后，跨模块六声明检查和最终完整门均通过。不能仅凭源码有
声明或模块编译成功判定接口实际存在；不删除必需声明审计来绕过失败。

前一检查点的 6 个模块闭合原无限加法、原配数及域内候选赋值全集公式的绝对性。
`PowerlessAdditionIteration` 给原迭代的实际后继方程、同值和自然数值域；
`PowerlessAdditionIterationCut` 以有限加法逐点定义整个实际 F，再由
F⊆A 推出 F∈D(A)。`PowerlessStageAdditionIteration` 将 F 放入 Cω+2
及所有 α>ω 的 proper 极限 Cα。`PowerlessAdditionAbsolute` 独立证明
原迭代正文绝对性，再用 F 的成员性处理原加法存在量词。
`PowerlessPairingAbsolute` 保留原无限加法与原配数模板，实际层出口
消去迭代图闭包；只需首坐标自然，不额外限制第二坐标和输出。
`PowerlessAssignmentsAbsolute` 用有限图闭包处理环境全称量词中的
候选 f。其 S 已作为域内参数给定，不把 S⊆Cα 误报为 S∈Cα。

用户质疑 T₃ 是否与 Z₂ 同强度后，已核对原文与实际定义。完整背景对应
文献的三阶集合论呈现，不是纯无幂集核心；文献中的模型/一致性比较
仍未在本仓库形式化。`ThirdOrderOmegaOne.of_power_l` 将必要假设拆为
核心、指定幂集及其良序，原 exists_l 不再经过全集规模界接口；
`ThirdOrderSelection.of_choice_l` 只需核心与集合良序化。34 个指定正向
出口的类型和正文常量依赖检查通过，未引用规模界，但这不等于已经
泛化全部主接口或严格降低一致性强度。明确口径见 THIRD_ORDER_BACKGROUND
第 5.1 节，独立强度复核求助为广场 #321（发帖时未有答复）。

第 47 节已完成原有限层分类证书、全部有限赋值上的查询一致及 Cκ
中 stable_m 的内外解释。D⊆N、N∈ω 的有限集合证书成员性已另由
内部自然数归纳证明，不是套用有限函数图闭包。下一步核对反射合同
所需早层的解释条件，再接内部 BM4 复杂度重编号和反射合同。
原层次图内外一致和成员性、stage/system 模板及域内图的一般前史
均已闭合，不再列作缺口，也不能推广为所有 proper 早级已有 Core。
原 slice/point、family/operator 的所需 Cκ 成员性及
公式解释已闭合，不能继续列为缺口。整个 F 的成员性、同一 F 的自然数
前缀及原有限递归公式解释也已完成。成员性与正文绝对性仍须分别核验。
不要对无限前史套有限图闭包。PowerlessEvaluationPrefixRestriction
才是同一求值图的自然数有限前缀；PowerlessEvaluationRestriction
比较不同赋值域的求值子集。BM4 重编号/反射合同、
任意下降实数检查器、标准类型化解释和精确强度校准仍开放。
本轮最终全门会话 59700 返回 exit 0；没有遗留的本轮构建进程。

此前 5 个模块已证明整个实际三角数图 T 属于 Cω+2，并属于每个高于
ω 的 proper 极限 C 层。`PowerlessTriangularFinite` 用原纯公式内部
ω 归纳核验全部内部有限三角数轨迹与实际 T 的值对应；
`PowerlessTriangularFiniteSyntax` 保留原 Formula，后继方程调用有限加法。
`PowerlessTriangularFiniteAbsolute` 只以有限图闭包取回轨迹和加法见证，
不假定 T 已属于成员域。`PowerlessTriangularCut` 逐点证明成员公式定义
实际 T，再将整个 T 放入 D(A)，输入仅为 T⊆A 而非 T∈A。
`PowerlessStageTriangular` 从 Cω 中的自然数有序对得到 T⊆Cω+1，
`second_l` 构造 Cω+2 的实际层见证，`limit_l` 传入 proper 极限层；
`parameters_l` 合并 ω、e、T、t₁、t₂、t₃ 的层成员性。

此前 5 个模块已证明原函数图判定的传递子域绝对性、有限加法见证与
原无限迭代加法的等价，以及任意高于 ω 的实际 C 层的有限加法正确
解释（不要求该层是极限层，含 Cω+1）。`PowerlessSourceGraphAbsolute`
覆盖原配对、有序对、取值、映射；见证由传递性取回，无须子域核心。
`PowerlessAdditionFinite` 精确给 n+1 长自然数值轨迹及与原加法的等价；
`PowerlessAdditionFiniteSyntax` 使用原 Formula 表示有限轨迹及值。
`PowerlessAdditionFiniteAbsolute` 分别核验轨迹正文和存在见证的传输，
`finite_l` 只要求第二加数自然，`addition_l` 对两个自然加数连接原加法。
`PowerlessStageAdditionFinite.graphs_above_l` 从 Cω 中的有限图向任意
更高层传输，`stage_l` 消去闭包前提，原无限迭代图没有被假定落级。

此前 4 个模块已闭合实际 D 算子、非零极限层的配对/并/后继闭包，
以及全部内部有限赋值图的层成员性。`PowerlessOperatorClosure` 用
原源公式覆盖将指定集合放入 D(A)，显式处理空域；
`PowerlessStageClosure` 把两个参数移入共同早级，再用层次方程纳入
极限层。`PowerlessStageGraphClosure` 给有序对、添元及函数图追加。
`PowerlessStageFiniteGraphs.finite_l` 以原纯公式作内部 ω 归纳，证明
α 为非零极限且 ω⊆α 时，每个内部 n∈ω 和实际 f:n→Cα 都有 f∈Cα；
`first_l` 特化到 Cω。全部有限图的集合只证明为 Cα 的子集，不是元素。

此前两组共 7 个模块已证明全部实际 C 层的内部序数高度和原 ω 公式
在适当层中的正确解释。`PowerlessSourceAmbient` 给传递成员域到原模型
的原 Lévy 嵌入；`PowerlessOrdinalBounded` 给有界序数公式、原 Δ₀ 证书、
与原 `PowerlessOrdinal.ordinal_m` 的语义等价和传递子域绝对性。
`PowerlessOrdinalCut` 将指定序数截面实际放入 D(A)，空域独立处理；
`PowerlessStageOrdinal` 用纯公式内部序数归纳证明 Cα∩Ord=α。
`PowerlessStageParameters` 给 Cω 含全部内部自然数但不含 ω，以及
α>ω 时 Cα 包含 ω 和实际四个标签。原有模块均未替换。

`PowerlessSourceNaturalAbsolute` 已核验原空集、子集、后继和归纳集合
判定的传递子域绝对性；`PowerlessSourceOmegaAbsolute` 在实际 ω 已属于
域时，由内外两边最小性比较证明原 `omega_m` 恰识别这个 ω，并接到
实际高于 ω 的 C 层。不能删去 ω∈A 前提或假定 Cω 含 ω。
这些证明不假设成员域自身满足无幂集核心，不用外部 Acc。

前一阶段的 10 个模块完成一般原 Formula 的域/参数无关有限编译界、
同码分类与统一参数覆盖，以及固定源公式的有限反射预算和实际层出口。
`PowerlessSourceComplexityTotal.formula_l` 先于域、求值器及参数给内部
有限双极性编译界；真正有界量词不升层的规则另行保留。
`PowerlessLevyWitness` 和 `PowerlessSourceLevyWitness` 通过一次上域
编译及指定存在节点反射实际见证，不假定两域独立编译同码。
`PowerlessSourceReflectionTotal.formula_l` 再给任意两域及全部参数统一
有效的有限反射层号；`PowerlessStageSourceReflection.formula_l` 将其
接到实际 C 层的 n 层稳定，非空性、包含和系统对应均从已证接口取得。

接下来须处理旧算术/编码公式的实际绝对性。`PowerlessPairingCode.code_m`
明确调用原 `PowerlessAdditionSyntax.addition_m`，其见证是整条 ω 递归图；
不能只因有限加法同值、T 已落级就把旧编码及求值模板视作已绝对。

1. 对自然数 a 的实际加法迭代图 F，用有限加法公式在 Cω+1 上定义
   p∈F。由迭代唯一性把有限加法值与这个指定 F 的值对应，逐点核验后
   用原源覆盖把 F 放入 Cω+2，并传入 proper 极限层。此步尚未实现。
2. 核验原 `PowerlessAddition.iteration_l` 对已有域内 F 的绝对性：
   正向用原图和后继绝对性取回量词见证；反向在 a∈ω 时由原 range_l
   将值域重新选为实际 ω。`PowerlessRecursionSyntax.recursion_formula_l`
   不要求核心模型假设，可接原纯公式。再用 F 落级处理原加法的存在量词。
3. 连接原 `PowerlessPairingCode.code_m`，保留原加法/配数/求值模板，
   随后推进 assignments_m、evaluation_m、hierarchy_m、system_m 的解释
   及所需集合见证。不可假定任意 proper 极限层已有完整核心或收集闭包。

ω、标签、T 的早级成员性、三角数有限成员公式解释、原 ω 公式、
极限层有限图闭包及有限加法解释不再是缺口。
随后核验稳定/层次源模板在小层成员结构内的解释与外部 C 关系的
对应，再完成具体 BM4 重编号及反射合同。不要将
“固定源真值可反射”误报成层次定义绝对；一般编译预算与反射预算也没有
宣称最小或逐值相等。详见 `THIRD_ORDER_BACKGROUND.md` 第 31—38 节。
任意环境下降实数的 BM4 标签/检查器及类型化三阶解释、强度校准仍未完成。

`SecondOrderMemberCollection` 已完成下文历史待办第 1 项的实际装配。
新的 `Powerless*` 模块已从明确的无幂集核心完成：纯公式分离与精确像集、
实际集合函数图及其外延、精确限制、相容函数族之并、笛卡尔积、沿单射传回幂集、内部 ω 归纳与传递性、内部
良序的公式归纳。`ThirdOrder*` 已明确工作公理，验证共同实数界、内部
Cantor 及 P(P(ω)) 不存在，未新增 BM4 或反射公理。

已从实际函数图、`PowerlessRestriction.exists_l` 的限制与
`PowerlessFunctionUnion.exists_range_l` 的相容并推进内部递归。后继边界、
零／后继分解、自然数可比性已由 `PowerlessNaturalStep` 与
`PowerlessNaturalCompare` 完成；`PowerlessCoordinates` 已构造精确坐标集，
所以相容并不再预设各局部图有共同值域。`PowerlessTrace`、
`PowerlessTraceUnique` 已完成有限轨迹的存在唯一性和跨长度相容性；
`PowerlessOmegaRecursion` 已收集轨迹并构造内部 ω 递归函数，核验初值、
全内部后继方程及唯一性，`PowerlessRecursionSyntax` 提供结论纯公式。
`PowerlessCollapse` 已构造内部良序坍缩，`PowerlessOrderType` 已验证
到上游内部序数的实际双射及关系对应。`ThirdOrderOmegaOne` 已经通过
良序化 P(ω)、内部序型和分离极小元构造唯一首个不可数序数 κ，暂不需要
先构造 ω×ω 的自然数编码。这些证明没有调用宿主 WellFounded。
`ThirdOrderSelection` 已从纯公式收集上界及该界的良序构造实际选择图；
`ThirdOrderCountableFamily` 已统一选择单射见证，并将并集嵌入“族 × ω”。
为完成可数取界，已由实际 ω 递归构造内部加法，验证纯公式、存在唯一性、左右零律、
结合律、左右后继律、交换律、严格单调性及消去律，均已通过全量审计。
三角数编码 T(a+b)+a 已由 `PowerlessTriangular*`、`PowerlessPairingCode`
和 `PowerlessNaturalPairing` 完成：实际纯状态算子、全内部坐标不变量、
三角数递推与严格单调、对角线区间不交、ω×ω→ω 的实际单射均已审计。
`PowerlessProductMapping` 提供逐坐标乘积图；`ThirdOrderCountableUnion`
证明可数积与可数并，`ThirdOrderCountableImage` 证明子集及满射像保可数。
`ThirdOrderCountableSuccessor` 证明可数后继、κ 极限性；
`ThirdOrderCountableBounds.strict_l` 证明任意可数域上的 κ 值函数有 κ 内
严格上界，`omega_l` 覆盖全部内部 ω，`no_cofinal_l` 排除可数共尾函数。
可数取界检查点共新增 12 个 Lean 模块、74 个被审计声明。具体装配见
`THIRD_ORDER_BACKGROUND.md` 第 10 节；不能把这些对象级结论提升成宿主 Acc。
随后新增 9 个模块、108 个被审计声明，完成实际前驱图与通用内部良序递归：
`PowerlessHistory`、`PowerlessWellRecursionSyntax/Unique/Union/Extension`、
`PowerlessWellRecursion`、`PowerlessWellRecursionPresentation`。
它们从总唯一纯算子推导唯一递归图，并核验原纯公式表示；不使用外部良基。
`PowerlessOrdinalRelation` 提供内部 ∈ 关系图及精确前驱域；
`PowerlessOrdinalRecursion` 消去辅助关系，以内部隶属给出递归存在唯一性
和纯公式表示。主入口为 `PowerlessOrdinalRecursion.exists_unique_l`。
有限赋值检查点新增 7 个模块、70 个被审计声明：`PowerlessAppendGraph/Family`
构造有限图的扩张及反向分解，`PowerlessFiniteAssignments` 在模型全部
内部 n∈ω 上构造精确的 n→A 图族，再收集其并。无需先做嵌套元组解码。
`ThirdOrderFiniteAssignments.all_exists_l` 证明 A 可数时全部有限赋值可数。
`PowerlessAssignmentUpdate` 给出保持域与值域的单坐标替换及唯一性。
`PowerlessPairingBounds` 和 `PowerlessFormulaNode` 证明新三角数节点编码
存在、唯一、单射及子码严格递减。求值器检查点新增 8 个模块、109 个被审计
声明，完成实际全内部编号求值器：`PowerlessFormulaConstructor` 与
`PowerlessEvaluationTags` 固定二元载荷及标签 0、1、2、3；
`PowerlessEvaluationClause/Step` 表示隶属、等号、与非、显式索引存在
量词的纯局部算子，从全部赋值集合分离真值子集并证明总唯一性；
`PowerlessEvaluationHistory/Recursion` 实例化内部序数递归，证明实际
求值图存在唯一、历史查询一致及全部内部编号的精确不动点方程；
`PowerlessEvaluationEquations` 给出四类构造子的分别方程及完整实际
参数/赋值/求值图的集合存在性；`PowerlessEvaluationPresentation`
核验该图的纯公式表示。全部仅需无幂集核心，不要求 A 可数或 P(A)。
求值族检查点新增 7 个模块、60 个被审计声明：
`PowerlessEvaluationSlice/Family` 从实际数码与有限参数分离子集并收集
精确像集；待定义元素采用末尾追加到槽 m 的约定，不再预留第 0 槽。
`ThirdOrderEvaluationFamily` 证明可数域上的输出族可数。
`PowerlessEvaluationAtoms/Parameter` 完成原子式及单个集合参数的实际
语义对应；`PowerlessEvaluationClosure` 证明传递域包含于输出且输出
传递，空域输出精确为 {∅}。`PowerlessEvaluationOperator` 量化掉 S、F，
给出总唯一纯算子及上述结构性质。源编译检查点再新增 7 个模块，并在节点模块
补非零引理，共新增 42 个被审计声明：实际非空成员结构、源槽环境与
图表示、新槽与旧槽不冲突、更新及原子语义对应；所有命题联结词数码；
任意充分长赋值的规格；存在/全称量词的实际图更新证明；最后由
`PowerlessSourceCompilation.formula_l` 得到完整上游 Formula 的实际 c,N
及已表示充分长赋值上的语义对应。覆盖检查点新增 6 个模块，审计
净增 33 个声明，已补齐实际源环境图与末尾容量的统一对齐：
`PowerlessSourceReservation` 先构造不依赖末尾 J 的容量界，再量化所有
足够大的 J 及槽环境；`PowerlessSourceSlots` 允许旧槽在 k 之前或恰为 J，
量词只在 J 前分配。源更新及量词接口推广为新槽不同于全部旧槽；原
`SourceCompilation.formula_l` 保持原规格，从新容量定理直接推出。
`PowerlessSourceExtension/Realization` 实际构造自由及绑定环境的有限图，
`PowerlessAssignmentPadding` 保留原值并填充预留域。
`PowerlessSourceCoverage.point_l` 给同一个数码和参数图对所有 x∈A 的
切片语义；`family_l/operator_l` 证明原输出族包含每个带有限参数源公式
定义的 A 的子集。不是反向解码或经典 Def 等价；非空前提显式保留。
层次检查点再新增 10 个模块，并补充 `SourceCoverage.domain_l`，
审计净增 53 个声明，已完成下述层次递归与结构性质。
κ 级检查点新增 6 个模块，审计净增 28 个声明，已完成单级/Cκ
装配和可数子集统一早级界。见证界检查点新增 8 个模块、42 个被审计
声明：`PowerlessEvaluationWitness` 显式提取存在规则的实际见证及更新图；
`PowerlessWitnessChoice` 将 p=((i,b),f) 上的选择关系总化并核验纯表示，
坐标唯一性保证真实请求不能误走缺省分支；`ThirdOrderWitnessChoice`
构造内部集合选择图；`ThirdOrderWitnessImage` 构造覆盖全部内部数码和
内部有限赋值的可数见证像。`PowerlessWitnessClosure` 给出两域见证条件
及纯公式，`ThirdOrderSkolemBound` 将可数像装入严格更后的可数早级。
`PowerlessSkolemStep` 给出严格两级步骤的纯公式；
`ThirdOrderSkolemSelection.exists_l/system_l` 实际构造 H:κ→κ，并与
同一个 Cκ、有限赋值集合 S 及求值 F 装配，每步增长且吸收前级见证。
闭包检查点新增 6 个模块并补自然数共同严格界，净增 45 个被审计
声明。`PowerlessFunctionIteration` 从真实自映射构造内部 ω 迭代图，
以纯公式内部归纳证明值域不离开原域，并核验实际迭代规格的纯表示；
`ThirdOrderSkolemSequence` 实例化 H，得到严格增大的真实序列。
`PowerlessOrdinalSupremum` 给值域之并的精确成员式、纯公式、存在唯一、
序数性、最小上界及严格有界族的并仍小于 κ；`ThirdOrderSkolemLimit`
证明每项属于这个精确并，初值严格低于该共尾极限，并给出可数 Cξ
由序列各级之并精确覆盖。不是任取一个较大的界。
`ThirdOrderSkolemParameters.bounded_l` 以原纯公式在内部 n∈ω 上归纳，
将任意实际 g:n→Cξ 的全部参数统一收进序列某一级，包含非标准内部
有限长度。`ThirdOrderSkolemClosure` 再取相邻后级的见证，真正证明
`closure_l ω U F Cξ Cξ`。其 `system_l` 同时构造 U、S、F、ξ、Cξ，
核验 α∈ξ∈κ、Cξ 可数/非空/传递且 Cξ⊆U。所有源文件已同步且编译；
无自有后台构建。这四处迭代/极限/统一落级/见证闭包缺口不要重复列出。

此前初等性检查点新增 8 个模块，并补实际更新图的值域收缩，净增 42
个被审计声明。`PowerlessEvaluationCompare` 以真实见证和更新图证明
两域存在规则及全部局部规则的比较；`PowerlessEvaluationAgreement`
将比较性质先纯公式化，再沿内部 ω 的 ∈ 归纳，证明全内部数码及全部
内部有限赋值上的一致，并实际构造子域求值器。
`ThirdOrderEvaluationReflection` 将它接到任意起点以上的同一个实际
Cξ；`PowerlessEvaluationRestriction` 核验同一码/小域参数的求值子集
精确为原子集与小域之交，并将该交放入实际小域求值族。
`PowerlessSourceInclusion` 核验成员/环境包含、项值与绑定压入及图表示
保持；`PowerlessSourceWitness` 在小域构造/填充参数，只用一个 U 求值器
编译一次子式，给出实际源见证准则；`PowerlessSourceElementarity`
对原 Formula 全部构造子证明带参数初等性；`ThirdOrderSourceReflection`
把源初等性与独立的全内部数码一致性装配到同一个 Cξ，未把二者混同。
以上均已同步、编译并全量审计；无自有后台构建。

此前初等对检查点新增 2 个模块，并加强非冻结的新闭包/反射接口以保留
已证的极限层号，净增 16 个被审计声明。`PowerlessSourceInclusion.compose_l`
证明真实环境包含复合；源初等性和内部求值一致性各自的 `interpolate_l`
经同一上域合成。`ThirdOrderCountableSuccessor.omega_mem_l` 证明 ω∈κ，
`PowerlessStagePair` 以原纯公式准确表达非零极限和 ω<ξ<β 端点。
`ThirdOrderElementaryPair.exists_l/system_l` 已从任意 α∈κ 构造
α∈ξ∈β∈κ、ω∈ξ、两个可数/非空/传递实际级及其求值器，证明两级间
原源初等性和全内部查询一致；`system_l` 也构造上层 U/S/F。已全量验收。

此前有界检查点新增 5 个模块、净增 36 个被审计声明。
`PowerlessBoundedQuantifier` 原纯公式化实际成员有界量词，证明更新后
成员 guard 读取原界值及仅凭传递性/子码比较的两域绝对性。
`PowerlessBoundedCode` 以成员、两次 NAND、存在四步构造同一个数码，
证明存在、唯一、严格子码界和任意求值器中的精确语义；i≠j 显式保留。
`PowerlessBoundedAgreement` 已给成员/等号/NAND/有界存在的同码局部
比较规则。`PowerlessSourceBounded` 构造真实 Lévy 嵌入及有界原像，
核验现有环境对应，再复用上游原 IsDelta0 的全构造子绝对性。
`PowerlessSourceBoundedCompilation.exists_l` 编译原有界存在并同时
输出指定 `code_l` 与规格，以新槽前提验证界项不被绑定更新。
五个模块全部编译并全量审计；独立三阶图无旧可构造或宿主序数导入。

此前证书检查点新增 3 个模块、净增 33 个被审计声明。
`PowerlessBoundedCertificate` 定义实际集合 D 的内部自然数界及逐码
生成规则，给 step/certificate/recognizes 的原纯公式与满足等价。
`PowerlessBoundedCertificateSound.sound_l/recognizes_l` 对所有内部
证书及其数码证明传递子域查询一致：先纯公式化命题，再沿内部 ω 归纳，
使用严格子码界；不调用外部 Acc，也不假定全初等性。
`PowerlessBoundedCertificateClosure` 用共同自然数界中的实际分离
构造证书并/添点，保持局部规则，证明零/成员/等号/NAND/有界存在的
识别闭包。内部有限性没有替换成宿主有限列表。三模块已全量验收。

此前 Δ₀ 检查点新增 5 个模块、净增 20 个被审计声明。
`PowerlessCertifiedLogic` 给全部布尔构造的同码证书与查询方程。
`PowerlessSourceCertified` 给带证书否定/有界存在/有界全称/guarded 存在；
guard 只用原 MembershipGuard，界项求值经显式 Term.eval_weakenBound
恢复到外层。`PowerlessSourceDeltaReservation.formula_l` 已递归原
IsDelta0 全部 12 个构造器，保持先容量界、后任意 J/环境的顺序，同时
输出 c∈ω、识别证据和规格。`PowerlessSourceDeltaCompilation.formula_l`
给普通槽环境特例；`PowerlessSourceDeltaCoverage.point_l/family_l` 给
实际参数图及统一末尾追加的覆盖，后者保留 c/g/B 和指定切片关系。
五模块已接入总入口与独立审计，全部正式验收。源覆盖已闭合，不要重做。

此前内部层号检查点新增 7 个模块、净增 96 个被审计声明。
`PowerlessLevyEntry` 用实际自然数记录 (c,n,p)，p=0/1 为极性；不是新
源 AST。`PowerlessLevyRule` 给有界基例、NAND 翻极性、成员有界量词、
正层 Σ 存在和严格升层规则的原纯公式及局部单调性。NAND/有界/存在
依赖严格较小公式码；升层仅可引用同一码的严格较低层，勿加入同层
自引用。`PowerlessLevyCertificate.class_l` 量化有内部自然数界的实际
记录集。`CertificateClosure` 给并/添点、基例、同极性单调及跨极性
严格升层；`PowerlessLevyGeneration` 给实际构造子分类闭包。
`PowerlessLevyZero.exact_l` 以纯公式内部码归纳证明零层恰为有界类。
`PowerlessLevySeparation.first_l/not_zero_l` 给任意普通 ∃i(假) 码在
第一层接受、零层拒绝的正负定理。它是语法分类区分，不是语义层级
严格性或强度下界。七模块已全量验收，第一层源覆盖现见下一段；
任意内部证书的条件性极性语义现见下方；一般有限复杂度合同仍待证。

第一层源覆盖检查点新增 6 个模块、净增 27 个被审计声明。
`PowerlessSourcePolarity` 映射原 LevyPolarity 到内部 0/1，并验证翻转。
`PowerlessLevyLogic` 给任意内部层号的 NAND/否定/合取/析取/蕴含的
同码分类与查询方程。`PowerlessSourceLevy` 给原源任意层的有界量词
和正层 Σ 存在/Π 全称编译；普通存在保留实际构造子后再证明更新图
语义，全称经否定/存在跟踪极性。
`PowerlessSourceLevelOneReservation.formula_l` 已递归原 IsLevel1
全部 9 个构造器，先预留容量后任意 J/环境的顺序不变，Δ₀ 分支复用
此前带证书覆盖并提升。`PowerlessSourceLevelOneCompilation.formula_l`
给普通槽环境特例，`PowerlessSourceLevelOneCoverage.point_l/family_l`
给实际参数图/填充/追加的统一覆盖，保留 c/g/B 及指定切片来源。
六模块已全量验收；原源 Σ₁/Π₁ 编译覆盖不要重做。

极性检查点新增 5 个模块、净增 55 个被审计声明，已全量验收。
`PowerlessEvaluationDirection` 给 Σ
向上／Π 向下的原纯公式；`PowerlessQuantifierDirection` 和
`PowerlessLevyLocalAgreement` 把实际见证、更新图值域恢复及求值器
构造子方程接成局部方向规则。`PowerlessLevyAgreement` 的
`agreement_l n` 真正只量化 n 层证书，`lower_l n` 量化全部 m∈n；
已给原纯公式、下降单调、零层一致及第一层的低层一致。
`PowerlessLevySound.sound_l/class_l` 以显式低层一致为前提，沿实际
数码作纯公式内部归纳，对任意内部证书证明相应极性保持。同码升层
和跨极性存在直接消费严格低层一致，不伪造码递减；`first_l/sigma_l/pi_l`
从零层绝对性消去该前提，给传递子域的第一层单向保持。
一般定理不是任意两域的全层绝对性，第一层也不是双向等价。

实际层检查点新增 6 个模块、净增 34 个被审计声明，已全量验收。
`PowerlessStageEvaluation` 给实际
层/全部有限赋值集合/求值图的联合纯定义、存在及唯一；
`PowerlessStageStability.stable_l n α β` 保留 proper 条件和 n 层
证书查询范围，量化六个实际集合见证，并证明任意指定系统上的读取
等价。它尚未经 BM4 复杂度重编号。
`PowerlessLevyComposition` 及 `PowerlessStageStabilityOrder` 已给
真实赋值图上的复合/插值、实际端点的层号下降/传递/插值/零层实例，
以及 n 层稳定导出 n+1 层证书的极性保持，低层前提由实际后继方程消去。
`PowerlessStableMinimum` 用纯公式分离和内部正则性，在固定 β 中
构造最小 n 层稳定下端点，并证唯一、最小及随层号单调。
`ThirdOrderStablePair.exists_l` 给任意早级以上同一对端点在所有内部
有限层稳定；`minimum_l` 为每个内部 n 给某个 β<κ 及其最小下端点。
固定 β 的最小元不等于可变上端点下的全局边界；后者现由下一段单独证明。

本次边界检查点新增 4 个模块、净增 34 个被审计声明，已全量验收。
`PowerlessStableBoundary` 实际分离
α∈κ 且有某个 β∈κ 的 n 层稳定后继的全部候选，内部正则性给最小
σ，并证明原纯公式、存在/最小/唯一/序数性/内部自然数层号。
`PowerlessBoundaryOrder.cutoff_l` 给 α∈σ、β∈κ 上的任意稳定层
m∈n；目标允许等于或高于 σ，仍须保留 β∈κ。候选下降、边界上升
单调、两端在边界内的统一支撑及无全层稳定后继也已证明。
`PowerlessBoundaryFamily` 定义实际 F:ω→κ 的纯图，值与边界精确
等价，图唯一、单调、可读取截断；`ThirdOrderStableBoundary` 从
已有稳定对对全部内部 n 构造边界，再用原纯总唯一关系收集唯一 F，
并由内部可数取界给共同严格上界 ρ∈κ。这不是宿主选择函数。
仅是 κ 相对、未经 BM4 重编号的有限层边界，不是全序数类最小全稳定边界。

下一步推进一般有限源复杂度界、BM4 复杂度重编号和反射公式合同，
再把已证截断传给实际种子与展开。沿用同码证据和保护槽量词顺序；
勿由普通编译的规格猜测数码有证书。
原上游 LevyHierarchy 目前仅有 IsLevel1；更高层不能用另一个源 AST 替代。
一般极性保持已由显式低层一致处理同码升层；若后续要同时导出低层
一致，仍须独立验证相应层号归纳或稳定性前提，不能循环引用。然后完成
所需复杂度重编号及种子/展开合同；原始分层关系、下降单调、固定
上端点最小元、κ 内可变后继边界及层号截断已证，不能将所有层号
替换为同一个全初等关系。源初等性和内部全码
一致性及 proper 初等对已完成，不要再次列作缺口。具体断点见背景文档
第 21—31 节；需保留真正有界量词和同一内部求值码，并证明新 C 层的
固定参数包含/绝对性，不能直接搬用旧 L 层十三参数定理。
随后还须核验所需 Def/L 对应或当前 C 层次的原证明性质，并将实际 BM4 检查器
接入内部自然数。规约及任意环境下降实数 X 的处理见
`THIRD_ORDER_BACKGROUND.md` 第 6 节；该规约尚未证明。

已核对旧 API：`SecondOrderEvaluationFixedPoint` 和
`SecondOrderSourceSatisfaction` 使用实际 Z₂ 双类型模型及数值赋值码；
后者还要求原成员域的满数值呈现。它们不能直接用于潜在不可数的 Lκ。
旧 `SecondOrderFormulaCode` 使用平方配数，不等于本轮三角配数。
局部纯算子、求值族、完整上游公式编译、实际参数环境图、固定末尾容量
及统一有限参数覆盖现已完成，不要重做。实现采用源 AST 递归给统一
预留界，不另加量词深度语法或预留链。成员结构的非空前提显式保留；
空域输出 {∅} 已证明，详见背景文档第 16 节。
`PowerlessEvaluationImage` 已给任意集合上的算子像映射、满射及精确值域；
`PowerlessHierarchyStep` 已构造任意历史 H 的算子像之并，证明总唯一及
纯公式表示。`PowerlessEvaluationHierarchy` 已把它实例化到任意内部序数，
给唯一实际函数和精确方程 Cα=⋃{D(Cβ):β∈α}；`HierarchyPresentation`
给其纯表示。`PowerlessOrdinalInduction`/`OrdinalHistory` 提供纯公式的
内部 ∈ 归纳及真实前史域。
`HierarchyStructure` 已证明零值、嵌套和全部级传递；`HierarchyContinuity`
已证明后继算子方程、无末端指标的极限并方程，以及 Cβ∈Cγ（β∈γ）。
最后一项使用新 `SourceCoverage.domain_l`：A∈D(A)，包括空 A。
后继证明只用传递集 A⊆D(A)，没有假定一般 Def 载体单调。
`ThirdOrderHierarchyStep` 用实际可数像和可数并证明一步保可数；
`ThirdOrderEvaluationHierarchy.countable_l` 用实际纯公式内部归纳证明
任意给定图域内所有可数指标的层次值可数。以上已编译审计，不要重做。
`PowerlessHierarchyRestriction` 已证明初段限制保持完整前史及累计方程，
再用唯一性证明跨域前缀相容。`PowerlessHierarchyStage` 给含序数 guard
的单级纯定义、存在/唯一、原纯公式及任意较长图读值的等价。
`PowerlessStageStructure`/`ThirdOrderHierarchyStage` 接上此前所有结构
定理及可数级可数性。`ThirdOrderHierarchyLimit.system_l` 实际构造
U=Cκ、非空/传递证据、全部有限赋值 S 和求值图 F；全部早级可数并属于 U，
`union_l` 给 U 的精确早级并成员条件。成员结构不再要求数值满呈现。
`ThirdOrderHierarchyBounds.exists_l` 对每个内部可数 B⊆U，用单级纯公式
选择真实 B→κ 的级数图，再经可数取界/嵌套得到同一可数早级包含 B。
以上已编译审计，不要把相容、单级、Cκ 或可数子集早级界再列作缺口。
下一步构造 U 的纯量词见证选择关系（真实存在时给见证，无见证时用已证
非空值总化），在可数早级的全部有限赋值及内部自然数码上取可数见证像，
用统一早级界得到更后级。然后构造内部迭代、极限处的见证封闭及实际
Tarski–Vaught/反射对应。Cκ 内有共同界不等于某个迭代极限以下已经封闭；
内部有限参数的统一落级义务也不能略去。经典 L 等价仍未证明。
局部不可识别码为空；带非法子码的可识别节点仍按规则递归求值，不保证
所有非法码都为空。不要将模型全部自然数直接当作上游合法公式 AST。
具体已证接口和下一处断点见 `THIRD_ORDER_BACKGROUND.md` 第 13—19 节。
广场 #245–249 的审计已读；#256 更正了理论包含方向、P(ω×ω) 拉回所需的
正确目标幂集，以及可数上确界必须先有可数并/取界证明的逻辑边界。

本轮未提交、推送、清缓存或更换工具链。新增三阶审计已接入本地检查脚本
和待发布的 CI 配置，但远端 CI 未运行。两个最终证明版本仍须等新证明闭合。

## 以下保留额度停工时的历史记录

日期：2026-09-13。停止原因：普通 Codex 额度实时显示已用 50%、剩余 50%，
触发用户预先要求的整理停工条件。没有消费重置信用、提交或推送仓库。

## 当前结论

**尚未证明 BM4 的良序性可在 Z₂ 或一个已校准的略强标准背景中完成。**
原有宿主层 BM4 良序性定理未修改；当前增加的是降低背景的内部解释基础。

已完成的主线包括任意 Z₂ 模型中的完整 TMC 图解释及闭句推导传输，内部
有限数码与历史，唯一可定义操作的集合迭代和秩递归，统一内部求值关系，
上游有类型纯集合源公式的编译正确性，以及实际成员结构的可定义子集
收集上界。具体定理边界见 `SECOND_ORDER_BACKGROUND.md` 第 20—45 节。

最后两个已有模块是：

- `SecondOrderMemberFamily.exists_l`：同一内部族同时满足所有内部索引的
  成员代表不变性和全部上游源公式／有限参数的覆盖。
- `SecondOrderSubsetExact.mem_l`：显式相容选择图的切片对象对原成员根的
  成员条件，精确等于选择关系 F(i,n)。

已有收集集合 H **仅证明为上界，不是精确 Def(A)**。外部有类型源公式的
归纳与模型全部内部语法编号的解释必须继续区分。

## 恢复后的最近工作

1. 将 `SecondOrderMemberFamily.exists_l` 与
   `SecondOrderMemberNormalizer.code_fixed_l` 组合，导出原母根所有子节点
   上选择图的双模拟相容性，再接 `SecondOrderSubsetExact.mem_l` 和
   `SecondOrderSubsetCollection.exists_l`。这是已有接口的待做拼接，不应
   因接口各自编译通过而说组合定理已经完成。
2. 完成原图商内的语法／有限参数对象与全部内部公式编号的对应，区分合法
   内部语法与无效编号，证明精确的 Def 操作；补齐非空前提以外的边界情形。
3. 再构造可构造递归和正确的 L*，证明所需收集、选择及固定公式反射，接到
   精确的固定高度 BM4 目标。
4. 构造实际原始递归证明生成器 p，并在 PRA 中验证
   `∀ h, Proof_Z₂(p(h), code(W(h)))`，即 `(G)`。不能把 Lean 的闭句
   `Derives` 存在性当作原始递归证明码生成或 PRA 核验。

候选 `Z₂ + RFN_{Π¹₁}(Z₂)` 仍依赖 `(G)` 等未完成义务；反射方案只使用数
参数。它目前是有条件的候选，不能宣称已经提供了用户要求的略强上界。

## 本地工作树与验证

主目录：`C:/Users/17857/Documents/Codex/2026-07-24/zhe/YesMetaZFC-stage4`。
验证目录：`C:/Users/17857/Documents/Codex/bm4v/ConstructibleBridge`。
基点：`57da9d318df393b1ededbc93cd3abc745c8c8675`；分支：
`refactor/bms-slimming`。工作树含多轮未提交改动，不能整树覆盖或重置。

最后检查点名：`member-family`。证据位于主目录的同级 `outputs/`：
`bms-z2-member-family-bridge.log` 和 `bms-z2-member-family-audits.log`；
最终数字及验证范围见 `FINITE_BOUNDARY_VERIFICATION.md` 最后一节。

继续前先核对实时额度和用户的新授权。构建必须串行、单 Lean 工作线程；
根工程使用 Lean 4.33.1，桥工程使用 4.33.0-rc1，不要改工具链或共享冲突
的构建输出。主树编辑后同步到短验证树，并比对源码哈希。450 条历史桥接
警告是既有基线，禁止新增警告或关闭 linter 来掩盖问题。

保留原 ℒ 源签名、上游语法和 `_l`／`_m`／`_d` 命名层次；禁止占位证明、
新增公理或将内部良基偷换成外部 `Acc`。数值二进制码不自动等于原 β 编码。
本次本地验收不能表述为冷缓存验证或远端 CI 通过。


## 任务4：补齐任务1遗漏的整批验收（2026-09-16，WorkBuddy）

本批**不新增 Lean 数学代码**，只补最初要求但未留证据的整批验收。
本机全部命令单 Lean 线程串行执行，未提交、未推送、未覆盖既有改动。

### 1. 桥目录不带 target 的完整默认构建

`lake build`（cwd `bm4v/ConstructibleBridge`，LEAN_NUM_THREADS=1）：
**rc=0，2303 jobs，22.6s**（增量，日志中均为 Replayed，无新增警告）。

job 数对照（同一环境连续三次）：

- `lake build BMSConstructibleBridge`：rc=0，2297 jobs
- `lake build BMSTools`：rc=0，1396 jobs
- `lake build`（两个 @[default_target] 全含）：rc=0，2303 jobs

**2303 − 2297 = 6 jobs，差异来自目标范围**——第二个默认目标 BMSTools 自身
的模块；不是源码变化。佐证：两工作树 1512 个 `.lean` 内容完全一致、
163 个冻结资源未变、`git diff --check` 两树均通过。

### 2. 五个审计模块实跑（`lake env lean`，均 rc=0）

| 模块 | 结果 | 源 sha256 前 8 位 |
|---|---|---|
| `BMSConstructibleBridge/AxiomAudit.lean` | rc=0（#guard_msgs 机器校验，无输出即通过） | 9bcb88f3 |
| `BMSConstructibleBridge/FiniteBoundaryAudit.lean` | 79 个声明；无全层反射导入；仅三项标准公理 | 60d87c03 |
| `BMSConstructibleBridge/SecondOrderAudit.lean` | 2845 个声明；无可构造语义或 Ordinal 导入 | b9d0853d |
| `BMSConstructibleBridge/ThirdOrderAudit.lean` | 3010 个声明；62 个出口未引用全集规模界 | 10942f37 |
| `BMSTools/Audit.lean` | 3164 个依赖声明；仅三项标准公理 | 86a776b1 |

ThirdOrderAudit 为本批现跑，不引用旧日志，源哈希已记录以便下批比对。

### 3. 完整桥声明公理扫描（本次补做；精确覆盖见任务6第1、2节）

现成审计各只扫自己的模块白名单，入口 `BMSConstructibleBridge.lean` 也只导入
674 个模块中的 421 个。本次补做全桥声明扫描，精确覆盖见任务6第1、2节。

做法：在仓库之外（会话目录）生成临时 Lean 文件导入桥内全部有 olean 的模块，
对 `BMSConstructibleBridge.*` 前缀的**所有**声明做 `collectAxioms`，
只允许 propext / Classical.choice / Quot.sound：

**rc=0，扫描 670 个模块 / 8506 个声明，非标准公理依赖 0 个。**

未纳入的 5 个文件（AxiomAudit、FiniteBoundaryAudit、SecondOrderAudit、
ThirdOrderAudit、BMSTools.Audit）不进 lib 构建、无 olean，由第 2 节单独实跑覆盖；
BMSTools 的 4 个模块由 `BMSTools/Audit` 覆盖。

### 4. 禁止项扫描（桥内 682 个 `.lean`）

sorry 0、admit（作为证明项）0、axiom 声明 0、native_decide 0、关闭 linter 0。

`maxHeartbeats` 9 处（7 个文件），**全部落在 163 个冻结基线之内**，属既有写法；
非冻结文件新增 0 处。全仓库其余命中在上游 `YesMetaZFC/` 自动化代码内，与桥无关。

### 5. git diff --check 与冻结资源

两树 `git diff --check` 均 rc=0，无空白错误。

163 个冻结资源：main 长路径树 **163/163 原始字节一致**；bm4v 短路径树原始
只有 2/163 一致，**CRLF 归一化后 163/163 一致**——bm4v 全树行尾为 CRLF、
main 全树为 LF，冻结资源实际未变。

### 6. 两工作树源码 SHA256 核对

1512 个 `.lean`，文件集合一致（无仅单边存在的文件）。
原始哈希不一致 185 个；CRLF 归一化后仍不一致 24 个；**再去掉行尾空行后
1512/1512 全部一致**。差异全部是行尾（CRLF/LF 与文件末尾空行），**零语义差异**。

### 7. 本批发现（未处理，留给下批裁定）

- `bm4v/docs` 比 main 少 5 个文件：`FINITE_BOUNDARY_VERIFICATION.md`、
  `FIXED_HEIGHT_Z2.md`、`SECOND_ORDER_BACKGROUND.md`、
  `THIRD_ORDER_BACKGROUND.md`、`legacy-resource-baseline.json`（冻结基线只在 main 有）。
- 5 个独立审计文件不在任何 lake 目标内（无 olean），只能靠
  `scripts/check-all.sh` 或 `lake env lean` 单跑；默认构建不覆盖它们。

### 8. 未做／未核（不要把本批说成全门通过）

- **未跑根项目构建**（按指令不需要，且根/桥不可并行），远端 CI 未跑。
- 本次为**增量**构建（全部 Replayed），**不是冷缓存全量重编译**。
- 本批语义验收**仅限共同反射层**；稳定对与 Z₂ 终局仍未完成。
- 未提交、未推送。

## 任务6：补齐全桥扫描源码时效与失败门，并安全对齐交接（2026-09-16，WorkBuddy）

本批是任务4的补验，不新增 Lean 数学代码，未提交、未推送。全部命令单 Lean 线程串行。

### 1. 全模块由 Lake 显式请求（不再按 has_olean 筛选）

模块集合来自**源码枚举**：`bm4v/ConstructibleBridge` 下 `BMSConstructibleBridge/` 与
`BMSTools/` 的全部 `.lean`，**共 674 个**；显式排除、且仅排除那 5 个独立审计文件
（`BMSConstructibleBridge/{AxiomAudit, FiniteBoundaryAudit, SecondOrderAudit, ThirdOrderAudit}`
与 `BMSTools/Audit`）——不再按"缺 olean"静默跳过任何其他源码。

- 模块清单：`bm4_t6_module_list.txt`
- 命令：`lake build <每批 60 个模块>` × 12 批，cwd `bm4v/ConstructibleBridge`，LEAN_NUM_THREADS=1
- 结果：**12/12 批 rc=0**，总 55.4s，**缺模块 0**
- 日志：`bm4_t6_lake_all_modules.log`（含每批实际模块与 rc）

结论：默认入口只直接 import 421 个模块，但这 674 个模块**全部**在当前 Lake 依赖闭包内、
源码与依赖哈希核对通过。允许正常增量（全部 Replayed），未清缓存、未强制冷重编。

### 2. 扫描器失败门修正与重跑

修正三处：

1. 集合改为源码枚举 + 仅排除那 5 个（原来按 has_olean 静默跳过）；
2. 意外公理非空时 `throwError` 使 **rc≠0**（原来只 `logInfo`，永远 rc=0）；
3. 导入核对按**源文件清单 vs `env.header.moduleNames`**，不再以"扫到声明的模块数"
   代替零声明模块的存在；`BMSConstructibleBridge` 与 `BMSTools` 分别计数。

重跑（48.2s，**rc=0**）：

| 指标 | 值 |
|---|---|
| 期望模块（其中 BMSTools） | 674（4） |
| 缺失模块 | 0 |
| 声明数（全桥） | 8506 |
| 有声明模块 / 零声明模块 | 670 / 4 |
| BMSTools 侧声明数 | 0 |
| 非标准公理依赖 | 0 |

**BMSTools 侧 0 声明是正确结果，不是漏扫**：BMSTools 的非审计模块只有
`Assignments` / `Certificates` / `Recursion` / `Sets` 四个，均为纯 import 聚合文件
（各 10–11 行，只做再导出，无自有声明），声明全部归属 `BMSConstructibleBridge.*`；
BMSTools 的传递依赖声明由独立审计 `BMSTools/Audit.lean`（3164 个依赖声明）覆盖。
旧版按"有声明的模块数"汇报会把这 4 个静默漏掉——这正是本次要补的口径。

**失败门自测**（不改仓库、不引入临时 axiom，只把白名单置空）：
rc=1，`T6_FAIL missing=0 unexpectedAxioms=5597` —— 门确实会红，不是恒绿。

本批源码与构建产物未变（只动 docs），五项独立审计仍有效；为刷新证据已串行重跑，
结果与任务4一致：AxiomAudit / FiniteBoundary（79）/ SecondOrder（2845）/
ThirdOrder（3010）/ BMSTools（3164）**全部 rc=0**。

脚本与日志（均在会话目录，仓库外）：`bm4_t6_full_scan.py`、`.lean`、`.log`，
`bm4_t6_gate_selftest.py`、`.lean`、`.log`。

### 3. 两树哈希：三档口径分开报告（不再混写）

转换规则：`raw` = 原始字节 sha256；`crlf` = CRLF→LF 归一化；
`norm` = 在 `crlf` 基础上再剔除文件末尾空行。

全量 1512 个 `.lean`：

| 口径 | 一致 | 不一致 |
|---|---|---|
| raw 原始字节 | 1327 / 1512 | **185** |
| CRLF 归一化 | 1488 / 1512 | 24 |
| 再剔除末尾空行 | **1512 / 1512** | 0 |

**raw 口径下两树源码并不全同（185 个不同）**，原因是 bm4v 全树 CRLF、main 全树 LF。

本批三文件：

| 文件 | raw（两树） | raw 相同 | norm 相同 |
|---|---|---|---|
| `BMSConstructibleBridge/PowerlessSourceReflectionFamily.lean` | `7217ea5a…` | 是 | 是 |
| `BMSConstructibleBridge.lean`（聚合入口） | `135b1d74…` | 是 | 是 |
| `BMSConstructibleBridge/ThirdOrderAudit.lean` | `10942f37…` | 是 | 是 |

163 个冻结资源：main 长路径树 163/163 **原始字节一致**；bm4v 短路径树 raw 仅 2/163 一致，
CRLF 归一化后 163/163 一致。两者分开报告，不合并写成"冻结资源一致"。

### 4. docs 安全同步

- 缺失的 5 个文件已从主树复制到短树，复制**前**二次验证目标不存在，复制后字节一致：
  `FINITE_BOUNDARY_VERIFICATION.md`、`FIXED_HEIGHT_Z2.md`、`SECOND_ORDER_BACKGROUND.md`、
  `THIRD_ORDER_BACKGROUND.md`、`legacy-resource-baseline.json`。
  5 个文件均**不在** 163 个冻结基线内。
- `SECOND_ORDER_HANDOFF.md`：短树旧内容 = 主树旧内容删去 309 行（唯一差异块
  `delete main[1:310]`，短树无任何独有文字），两树任务4小节 83 行逐行一致
  → 属纯缺失、无实质冲突，故**只插入**那 309 行，短树 915 → 1224 行，既有文字全保留。
- 已纠正未核的历史概括 2 处：「此前**没有**全桥声明扫描」改为「本次补做全桥声明扫描，
  精确覆盖见任务6第1、2节」。
- 同步后两树该文档**逐行完全一致，残留 diff 0**。说明：该文档短树现为 LF（与主树一致；
  短树其余 `.lean` 仍为 CRLF），未为此改写整树或冻结资源。

### 5. 未做／未核（不要把本批说成全门通过）

- 仍是**增量**构建（全部 Replayed），**不是冷缓存全量重编译**；
- 未跑根项目构建、未跑远端 CI；
- 语义验收**仅限共同反射层**；稳定对与 Z₂ 终局仍未完成；
- 未提交、未推送；两树工作区中他方既有未提交改动本批未触碰；
- `git diff --check` 两树均 rc=0。

---

## 任务7：夜间交接最终收束（2026-09-26/27，WorkBuddy，task #44 步骤 E）

截止线：2026-09-27 10:00 Australia/Sydney（= 09-27 00:00 UTC）。本节点为**最终快照上的独立验证收束**，
不使用任何旧源码对应的日志签收。

### 1. 快照与冻结交接口径

| 项 | 值 |
|---|---|
| HEAD | `013b0edbb7808bbefa2f2aaa5fc6d700196b3016`（2026-09-19 21:22:49 +1000） |
| 本轮 commit / push | **0 / 0** |
| `PowerlessBMSMatrixTransfer.lean` SHA256 | `17a58917e3c645657ecae90ebafda428f78180bb0d8bcd3ef54d833946ed514c` |
| `ThirdOrderAudit.lean` SHA256 | `7ebd4a63e40e00e6ac1b9a355740e6370172e6c49f57d2744dbb0437c20c0dc7` |
| 构建槽 | 17:09Z（悉尼 09-27 03:09）qwen3.8 交回；WorkBuddy 于 23:36Z 取槽（广场 #3115） |
| 并发 | 取槽时进程扫描：`lean`/`lake`/`leanall` 构建进程 **0**（仅 `lean-lsp-mcp.exe` 常驻，非构建） |

### 2. 最终快照串行验证（本轮实跑，非 Replay 沿用）

命令均为 `LEAN_NUM_THREADS=1` + `lake --wfail`，在 `ConstructibleBridge/` 子项目内串行执行，
保持仓库原有严格门槛（`--wfail` 令警告即失败）。

**目标 1 — `BMSConstructibleBridge.PowerlessBMSMatrixTransfer`**

- 命令：`LEAN_NUM_THREADS=1 lake --wfail build BMSConstructibleBridge.PowerlessBMSMatrixTransfer`
- 起止：2026-09-26T23:36:39Z → 23:37:19Z（40s）
- **rc = 0**，`Build completed successfully (1853 jobs)`
- 四出口 `#print axioms` 实测：

| 出口 | 位置 | axioms |
|---|---|---|
| `matrix_l` | :200 | `[propext, Classical.choice, Quot.sound]` |
| `matrix_at_l` | :201 | `[propext, Classical.choice, Quot.sound]` |
| `closed_l` | :202 | `[propext, Classical.choice, Quot.sound]` |
| `closed_from_candidate_sources_l` | :203 | `[propext, Classical.choice, Quot.sound]` |

- **`sorryAx` 未出现**（task42 修复目标达成）；警告 0。

**目标 2 — `BMSConstructibleBridge.ThirdOrderAudit`（聚合审计门槛）**

- 命令：`LEAN_NUM_THREADS=1 lake --wfail build BMSConstructibleBridge.ThirdOrderAudit`
- 起止：2026-09-26T23:37:26Z → 23:37:50Z（24s）
- **rc = 0**，`Build completed successfully (1956 jobs)`
- 日志：`.scratch/final_snapshot_thirdorderaudit_2350.log`（546133 B）
- 机械复算（`.scratch/_axiom_stat_final.py`，折行归一后全量解析）：

| 项 | 结果 |
|---|---|
| 出口总数 | **2191** |
| 公理组合 | 三项全 `1927`；`{Quot.sound, propext}` `176`；`{propext}` `85`；`{Quot.sound}` `3` |
| **非 `{propext, Classical.choice, Quot.sound}` 子集的出口数** | **0** |
| `sorryAx` | **0** |
| `warning` | **0** |

> 口径说明（承接任务 C 的纠正）：上表只说明**每个出口的 Lean 公理足迹不含对象理论公理**。
> 对象理论前提以函数参数（如 `hℳ : Theory.Model Models ℳ PowerlessTheory.theory_m`）传递，
> `#print axioms` **不显示**，故本表**不构成**"对象理论不使用 Collection/Separation"的证明。
> 对象层强度结论见「五之三」与下文第 4 节。

### 3. 三分级（已证 / 条件命题 / 主缺口）

**[已证]**

1. task42 修复：`matrix_at_l` 前向引用已解，四出口在最终快照 rc=0 且公理足迹为三项标准公理，`sorryAx` 消失。
2. 聚合审计：`ThirdOrderAudit` 1956 jobs rc=0，2191 出口公理足迹全部为三项标准公理子集，零警告。
3. **P2**：`no_chain_l` 的证明体**确实消费** `collection_l` 家族（机械穷举 2409 声明闭包）。
4. **P3**：`ω×ω` **不是**该链唯一的 `collection_l` 消费点 —— 至少 **2 类独立公理需求**
   （Ⅰ 内部 `ω×ω` 经 `PowerlessImage.exists_l:29`；Ⅱ `binary φ` 收集经 `PowerlessCollect.exists_l:25`），
   `no_chain_l` 证明体闭包内共 **4 个入口**。
5. qwen3.8 三块容器假设砖（`PowerlessBoundedWitness` / `PowerlessPairCoverGraph` /
   `PowerlessMappingOfContainer`）字面**不消费** `collection_l`/`image_l`，编译 rc=0。

**[条件命题]**

1. 三块砖是「∃-型存在性假设的参数化替代」，**不是** P1（Collection 可消去）的解决；
   它们**未接入任何消费者**，是孤儿出口。
2. 三块砖未覆盖第 Ⅱ 类消费点（`binary φ` 收集）。
3. `SecondOrderPureTransfer.correspondence_l`（`SecondOrderPureTransfer.lean:23`）是 **structure**
   （7 字段：`numberEquiv_l`/`setRel_l`/`zero_l`/`succ_l`/`add_l`/`mul_l`/`member_iff_l`），
   全树**无任何实例**。所谓"条件式迁移"的源侧语义条件由此 structure 承载，属**假设**。
4. "CI 增量数十秒～8 分钟、警告不增"依赖缓存状态与 runner 平台（本机 Windows 单线程 ≠ GitHub Linux）。

**[主缺口 / 未证]**

1. **★「每个固定外部 H 的 Z₂ Derives」是否真正闭合 —— 未闭合。**
   - 现有产物是**条件式**的：`closed_l` / `closed_from_candidate_sources_l` 的陈述把剩余义务
     压成源模型对目标集合候选的覆盖，并以 `correspondence_l` 这一**无实例 structure** 作为输入。
   - 语义条件桥（`hℳ` 下的 `Models` 假设、`correspondence_l` 字段）**不等于**最终形式化的
     "每个固定外部 H 的 Z₂ 真的 Derives"。把前者当作后者即为偷换目标。
   - 因此本节点的定级是：**对象层关节的 Derives 尚未接到 `SemanticallyEntails`**（与 qwen3.8 #3113 一致）。
2. **P1（Collection 可否消去）未证**：仅有草案与三块孤儿出口参数化替代，且已知需同时消去 **2 类**独立需求，
   成本高于此前估计。
3. `SecondOrderZeroHeight` 及 #3067 的 28 个孤儿模块落在所有 CI 路径外，**CI 永不编译**；接法未裁决。
4. 接入后整包官方 `lake build` 时间与 CI 警告门**未测**（需改受控入口，本节点不改）。
5. 宿主 `native_decide` 形态公理口径未定；宿主传递闭包**未审计**。

### 4. 明确未验证项（不用旧日志签收）

- 本节点**未**运行根项目（`YesMetaZFC.lean`）构建，**未**运行远端 CI。
- 上述两个目标为**增量**构建（大量 Replayed），**不是冷缓存全量重编译**；
  qwen3.8 侧 #2995 曾对 `SecondOrderZeroHeight` 做过冷编译（rc=0 / 1123 jobs / Built 34s），
  但该冷编译**不覆盖**本节点两个目标的全部依赖。
- `ThirdOrderAudit` 未包含 qwen3.8 的 25 项白名单接入（接法未裁决，本节点无写权变更入口文件）。
- 截至 10:00 若有任何目标未完成，本文件如实标注为未验证，**不引用旧源码日志**。

### 5. 具体下一步（待 Codex 一行裁决）

1. **接法裁决**：`SecondOrderZeroHeight` 及 #3067 的 25/27 项白名单，是并入 `lakefile.lean` 的 `globs`，
   还是 CI 加单目标白名单？（二者皆受控文件，本轮未改。）
2. **路线裁决**：候选 A（面最小，只需消去内部 `ω×ω`）、B（成本最高，须同时消去 2 类 Collection 需求）、
   C（走 `ThirdOrderStageCore`，未找到现成定理）三者选一。
3. **主缺口推进**：为 `correspondence_l` 构造至少一个实例，或改判其为显式假设并在最终陈述中标注；
   把对象层关节的 `Derives` 接到 `SemanticallyEntails`，闭合"每个固定外部 H 的 Z₂ Derives"。
4. 取得构建槽后跑一次冷缓存全量 + 整包官方构建，补上时间与警告门的官方读数。

### 6. 交付索引（本节点新增）

- 验证日志：`.scratch/final_snapshot_thirdorderaudit_2350.log`
- 统计脚本：`.scratch/_axiom_stat_final.py`
- 广场取证：`#3115`（取槽声明）；qwen3.8 侧 `#3113`（收束报告）、`#3025`–`#3111`（整夜取证链）
