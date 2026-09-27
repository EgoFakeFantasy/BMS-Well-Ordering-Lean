import BMSConstructibleBridge.SecondOrderProgramListMap
import BMSConstructibleBridge.SecondOrderProgramLength
import BMSConstructibleBridge.SecondOrderProgramListLookup
import BMSConstructibleBridge.SecondOrderListInduction

/-!
# 任务34 阶段C：带参数 mapIdx 折叠的逐内部下标对应

阶段A（`SecondOrderProgramListMap`，SHA `11CDAB88…` 已绿门冻结）给出
`map_m c = reverse ∘ extract ∘ fold (map_step c) ∘ call`，并已在任意模型给出真实一步
`map_step_rel_l`、末值提取 `map_extract_rel_l`。阶段B（`SecondOrderProgramListMapEntries`，
SHA `C0609952…` 已 #1772 窄验收）证得广义累计长度保持：折叠 `n` 个内部头项后，输出状态的
内层累计码恰比初始内层累计码多 `n` 项。本模块把该长度保持升级为**逐内部下标条目对应**。

`fold (map_step c)` 的累计槽是嵌套状态 `pair p (pair i acc)`：每消费一个头项 `a`，先在回调图
`C` 上取值 `mc = C (pair p (pair i a))`，再把状态更新为
`pair p (pair (succ i) (succ (value mc acc)))`——参数 `p`、当前下标 `i` 随状态携带，只有最内层
累计码 `acc` 在首部增加一项 `mc`。故累计码逐折叠恰好把每一项映射值压到表首。

本检查点先交**后 `m` 项保序**这一自洽小闭环（阶段B 已确立先交小闭环再写前段的节奏，
见广场 #1756/#1772）：设源码 `a` 长 `n`、初始状态 `v` 提取内层累计码 `va` 长 `m`、输出状态
`y` 提取内层累计码 `ya`。则对内部下标 `i < m`，`ya` 在位置 `add n i` 的读取值与 `va` 在位置
`i` 相同——即旧累计表整体右移 `n` 位、顺序不变。这一步与参数 `p`、起始下标 `i` 无关（回调值
只影响前段），但归纳谓词仍对任意完整状态全称量化，与阶段B 一致。

前 `n` 项倒序并携带回调值 `C (pair p (pair (add i k) a[k]))`、以及把 `extract ∘ fold ∘ call`
归约到 `reverse`、得到 `map_m c` 从零起逐内部下标取值规格，留待本文件后续检查点。全程用真实
`Formula` AST、语言检查与 `SecondOrderListInduction.list_induct_l` 在内部列表码上归纳；不假设
内部长度标准、不收集外谓词、图参数一律取实际 `graph_m`。越界补零（`lookup_past_end_l`）不进入
任一结论。

阶段C 不是 `copyBlock` 本身，也不是最终逐外部 n 的 Z₂ 良序／保守传输闭合。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListMapIndices

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic SecondOrderProgramListCode
open SecondOrderProgramListFold SecondOrderProgramListShift GraphSyntax PrimitiveFormulas
open SecondOrderProgramListMap
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLength (length_zero_l)
open SecondOrderProgramListIteration (iterate_m)
open SecondOrderProgramListLookup (lookup_m)
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-! ## 内部端：真实公式的广义累计器后段下标不变量（嵌套状态） -/

/-- 后 `m` 项保序不变量的实际公式。自由槽 `[a, F, L, E, K]`（`a` 为归纳列表码，`F` 为
`fold (map_step c)` 折叠图，`L` 为长度图，`E` 为实际累计读取图 `graph_m map_extract_m`，
`K` 为按位读取图 `graph_m lookup_m`）；正文从外到内绑定 `[v, y, n, m, va, ya, i, w]`：
`F(a, v)→y → E(v)→va → L(a)→n → L(va)→m → E(y)→ya → i < m →
(K(ya, add n i)→w ↔ K(va, i)→w)`。只用嵌套 `.imp` 作前件、末段 `.conj`（两个 `.imp`）表达
`↔`，使语义桥以 `simp only + rfl` 闭合。配对读取一律走 `output_m`／`edge_m` 原关系，不含非纯的
`.pair` 项。 -/
def entries_back_m : Formula signature_m [] [.num, .set, .set, .set, .set] :=
  (.forallE .num
    (.forallE .num
      (.forallE .num
        (.forallE .num
          (.forallE .num
            (.forallE .num
              (.forallE .num
                (.forallE .num
                  (.imp
                    (output_m (.fvar (.there .here)) (.fvar .here) (.bvar (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.bvar (.there (.there (.there (.there (.there (.there .here))))))))
                    (.imp
                      (edge_m (.fvar (.there (.there (.there .here)))) (.bvar (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.bvar (.there (.there (.there .here)))))
                      (.imp
                        (edge_m (.fvar (.there (.there .here))) (.fvar .here) (.bvar (.there (.there (.there (.there (.there .here)))))))
                        (.imp
                          (edge_m (.fvar (.there (.there .here))) (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there (.there (.there .here))))))
                          (.imp
                            (edge_m (.fvar (.there (.there (.there .here)))) (.bvar (.there (.there (.there (.there (.there (.there .here))))))) (.bvar (.there (.there .here))))
                            (.imp
                              (PrimitiveFormulas.lt_m (.bvar (.there .here)) (.bvar (.there (.there (.there (.there .here))))))
                              (.conj
                                (.imp
                                  (output_m (.fvar (.there (.there (.there (.there .here))))) (.bvar (.there (.there .here))) (Term.app (σ := signature_m) .add (.cons (.bvar (.there (.there (.there (.there (.there .here)))))) (.cons (.bvar (.there .here)) .nil))) (.bvar .here))
                                  (output_m (.fvar (.there (.there (.there (.there .here))))) (.bvar (.there (.there (.there .here)))) (.bvar (.there .here)) (.bvar .here)))
                                (.imp
                                  (output_m (.fvar (.there (.there (.there (.there .here))))) (.bvar (.there (.there (.there .here)))) (.bvar (.there .here)) (.bvar .here))
                                  (output_m (.fvar (.there (.there (.there (.there .here))))) (.bvar (.there (.there .here))) (Term.app (σ := signature_m) .add (.cons (.bvar (.there (.there (.there (.there (.there .here)))))) (.cons (.bvar (.there .here)) .nil))) (.bvar .here))))))))))))))))))

/-- 后段下标不变量公式属于原纯算术语言。 -/
theorem entries_back_language_m : language_m entries_back_m = true := pure_language_m _ rfl

/-- 实际公式在模型中的真值即后 `m` 项保序不变量：自由变量按 `a, F, L, E, K` 送入环境，
八个内层量化变量按 `v, y, n, m, va, ya, i, w` 从外到内绑定，逐段 `simp only` 展开
`output_m`／`edge_m`／`lt_m` 到 `relation_l`、`add_l` 与 `SecondOrderOrder.lt_l`，末段
`.conj` 两个 `.imp` 经 `iff_def` 收成 `↔`。 -/
theorem entries_back_syntax_l (F L E K : set_l ℳ) (a : num_l ℳ) :
    Formula.satisfies ((((((Env.empty (M := ℳ)).pushFree K).pushFree E).pushFree L).pushFree F).pushFree a)
      entries_back_m ↔
      ∀ v y n m va ya i w : num_l ℳ, relation_l F (value_l a v) y → relation_l E v va →
        relation_l L a n → relation_l L va m → relation_l E y ya → SecondOrderOrder.lt_l i m →
          (relation_l K (value_l ya (add_l n i)) w ↔ relation_l K (value_l va i) w) := by
  simp only [entries_back_m, Formula.satisfies, output_syntax_l, SecondOrderPairing.edge_l,
    SecondOrderOrder.formula_l, ←iff_def]
  rfl

/-- 广义累计器折叠的后 `m` 项保持累计原顺序：源长 `n` 时输出内层累计码 `ya` 的内部位置
`add n i`（`i < m`）读取值与初始内层累计码 `va` 位置 `i` 相同。对内部列表码 `a` 用真实公式
`entries_back_m` 作原列表归纳（`SecondOrderListInduction.list_induct_l`）。归纳器注入列表码
自由槽，故送进的环境只到最外层集合图 `K, E, L, F`，不含尚未绑定的 `a`。

空码基：`fold_zero_l` 给出 `v = y`，提取图函数性使 `ya = va`；源码 `0` 长 `0` 使 `add 0 i = i`，
两侧同读。cons 步：`fold_cons_l` 拆 `F(succ(pair a t), v)→y` 为 `S(v, a)→st` 与 `F(t, st)→y`；
先用 `SecondOrderUnpairing.surjective_l` 两次拆任意状态 `v = pair p (pair i va)`
（`map_extract_rel_l` 给出 `va` 为内层累计码），真实一步 `map_step_rel_l` 把 `st` 表为
`pair p (pair (succ i) (succ (value mc va)))`，`map_extract_rel_l` 给出 `E(st) = succ (value mc va)`，
`length_cons_l` 给出其长度 `succ m`。归纳假设在状态 `st` 上、界 `succ i < succ m`（`succ_iff_l`）
处得 `K(ya, add nt (succ i)) ↔ K(succ (value mc va), succ i)`；把 `add nt (succ i) = add (succ nt) i`
（`add_succ_l` 正向、`succ_add_l` 反向）重排，再用 `lookup_cons_succ_l` 把 `succ (value mc va)` 的后继位
归约回 `va` 的 `i` 位。全程只用真实图与已验 `length_*`/`map_*`/`fold_*`/`lookup_*` 引理，不假设内部
长度标准，不收集外谓词。 -/
theorem fold_back_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {C F L E K I : set_l ℳ}
    (hC : graph_semantics_l (graph_m c) C)
    (hF : graph_semantics_l (graph_m (fold_m (map_step_m c))) F)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m map_extract_m) E)
    (hK : graph_semantics_l (graph_m lookup_m) K)
    (hI : graph_semantics_l (graph_m iterate_m) I) :
    ∀ a : num_l ℳ, ∀ v y n m va ya i w : num_l ℳ, relation_l F (value_l a v) y →
      relation_l E v va → relation_l L a n → relation_l L va m → relation_l E y ya →
        SecondOrderOrder.lt_l i m →
          (relation_l K (value_l ya (add_l n i)) w ↔ relation_l K (value_l va i) w) := by
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ (map_step_m c)
  let hLf := function_of_semantics_l hℳ length_m hL
  let hEf := function_of_semantics_l hℳ map_extract_m hE
  have h00 : relation_l L (zero_l ℳ) (zero_l ℳ) :=
    (SecondOrderProgramLength.length_rel_l hℳ hL hI (zero_l ℳ) (zero_l ℳ)).mpr
      ((length_zero_l hℳ hI (zero_l ℳ)).mpr rfl)
  refine SecondOrderListInduction.list_induct_l hℳ entries_back_m
    entries_back_language_m
    (((((Env.empty (M := ℳ)).pushFree K).pushFree E).pushFree L).pushFree F)
    (fun a => ∀ v y n m va ya i w : num_l ℳ, relation_l F (value_l a v) y →
      relation_l E v va → relation_l L a n → relation_l L va m → relation_l E y ya →
        SecondOrderOrder.lt_l i m →
          (relation_l K (value_l ya (add_l n i)) w ↔ relation_l K (value_l va i) w))
    (fun a => entries_back_syntax_l F L E K a) ?_ ?_
  · -- 空码：v = y 使两侧提取相同，源码长度 n = 0，故 add 0 i = i，两侧同读。
    intro v y n m va ya i w hy hEva hla hlv hEya _
    have hv : v = y := (fold_zero_l hℳ (map_step_m c) hF v y).mp hy
    have hn : n = zero_l ℳ := function_value_unique_l hLf hla h00
    rw [← hv] at hEya
    have hyava : ya = va := function_value_unique_l hEf hEya hEva
    subst hn
    subst hyava
    rw [SecondOrderNumbers.zero_add_l hℳ i]
  · -- cons 码：先拆任意状态 v = pair p (pair i va)，真实一步推进 st，后段索引右移一位。
    intro a t ih v y n m va ya i w hy hEva hla hlv hEya hit
    rw [fold_cons_l hℳ (map_step_m c) hF hS a t v y] at hy
    obtain ⟨st, hsw, htw⟩ := hy
    obtain ⟨p, s, rfl⟩ := SecondOrderUnpairing.surjective_l hℳ v
    obtain ⟨ii, A, rfl⟩ := SecondOrderUnpairing.surjective_l hℳ s
    have hAv : A = va := (map_extract_rel_l hℳ hE p ii A va).mp hEva
    rw [hAv] at hsw
    obtain ⟨mc, _, hst⟩ := (map_step_rel_l hℳ c hC hS p ii va a st).mp hsw
    have hEw : relation_l E st (succ_l (value_l mc va)) := by
      rw [← hst]
      exact (map_extract_rel_l hℳ hE p (succ_l ii) (succ_l (value_l mc va))
        (succ_l (value_l mc va))).mpr rfl
    have hLsw : relation_l L (succ_l (value_l mc va)) (succ_l m) :=
      (SecondOrderProgramLength.length_rel_l hℳ hL hI
        (succ_l (value_l mc va)) (succ_l m)).mpr
        ((length_cons_l hℳ hI mc va m).mpr
          ((SecondOrderProgramLength.length_rel_l hℳ hL hI va m).mp hlv))
    have hnz : succ_l (value_l a t) ≠ zero_l ℳ := nonzero_l hℳ (value_l a t)
    have hspec :=
      (SecondOrderProgramLength.length_rel_l hℳ hL hI (succ_l (value_l a t)) n).mp hla
    rcases predecessor_l hℳ n with rfl | ⟨nt, rfl⟩
    · exact absurd ((length_zero_l hℳ hI (succ_l (value_l a t))).mp hspec) hnz
    · have hlt : relation_l L t nt :=
          (SecondOrderProgramLength.length_rel_l hℳ hL hI t nt).mpr
            ((length_cons_l hℳ hI a t nt).mp hspec)
      have hit' : SecondOrderOrder.lt_l (succ_l i) (succ_l m) :=
        (SecondOrderOrder.succ_iff_l hℳ i m).mpr hit
      have h := ih st y nt (succ_l m) (succ_l (value_l mc va)) ya (succ_l i) w
        htw hEw hlt hLsw hEya hit'
      rw [add_succ_l hℳ nt i, ← SecondOrderNumbers.succ_add_l hℳ nt i] at h
      exact h.trans (SecondOrderProgramListLookup.lookup_cons_succ_l hℳ hK mc va i w)

/-! ## 公理审计

本模块公共声明仅允许既有标准公理集合（propext/Quot.sound/Classical.choice），无新增公理，
亦不得有 `sorryAx`。审计置于命名空间内、`end` 之前。 -/

#print axioms entries_back_m
#print axioms entries_back_language_m
#print axioms entries_back_syntax_l
#print axioms fold_back_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListMapIndices
