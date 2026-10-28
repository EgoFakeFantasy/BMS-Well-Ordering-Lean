import BMSConstructibleBridge.SecondOrderProgramListMap
import BMSConstructibleBridge.SecondOrderProgramLength
import BMSConstructibleBridge.SecondOrderProgramListLookup
import BMSConstructibleBridge.SecondOrderListInduction

/-!
# 任务34 阶段B：带参数 mapIdx 折叠的内部长度保持与逐下标条目对应

阶段A（`SecondOrderProgramListMap`，合同由 Codex 接管修复，程序 AST 与公共声明不变，
SHA `11CDAB88…` 已绿门冻结）给出 `map_m c = reverse ∘ extract ∘ fold (map_step c) ∘ call`，
并已在任意模型上给出真实一步 `map_step_rel_l`、初值 `map_call_rel_l`、末值
`map_extract_rel_l` 与端点桥 `map_graph_rel_l`。本模块把折叠从“端点存在”升级为
**全内部长度保持**与**逐内部下标取值规格**，全程用真实 `Formula` AST、语言检查与
`SecondOrderListInduction.list_induct_l` 在内部列表码上归纳。

关键结构差异（相较阶段33 反转）：`fold (map_step c)` 的累计槽不是普通列表码，而是嵌套状态
`pair p (pair i acc)`。折叠 cons 递推（`SecondOrderProgramListFold.fold_cons_l`）每消费一个头项
`a`，把状态 `pair p (pair i acc)` 更新为 `pair p (pair (succ i) (succ (value (C (pair p (pair i a))) acc)))`：
参数 `p`、下标 `i` 均随状态携带，只有最内层 `acc` 增长一项。故本模块引入实际累计读取图
`E := graph_m map_extract_m`（`.comp .right .right`，复用 `map_extract_rel_l`），把任意状态
`v` 解到其内层累计码 `va`。由于模型每个数都可由配对逆式拆成 `pair p (pair i acc)`
（`SecondOrderUnpairing.surjective_l`），状态分解不引入“病态值”，故长度不变量可对**任意**
完整状态全称量化。长度不变量因此取
`F(a, v)→y → E(v, va) → L(a, n) → L(va, m) → E(y, ya) → L(ya, add n m)`，
即折叠 `n` 个内部头项后，输出状态的内层累计码恰比初始内层累计码多 `n` 项，与随状态携带的
参数 `p`、起始下标 `i` 无关。

后续逐下标层在此长度保持之上，把 `extract ∘ fold ∘ call` 归约到同一折叠的规范初值调用，
再用已验 `reverse` 前/后段下标对应，得输出映射表内部位置 `j < n` 的读取值与
`C (pair p (pair i aᵢ))` 的对应；一般起始下标 `k` 与一般累计列表 `acc` 均全称量化，不假设
内部长度标准、不收集外谓词、图参数一律取实际 `graph_m`。

阶段B不是 `copyBlock` 本身，也不是最终逐外部 n 的 Z₂ 良序／保守传输闭合。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListMapEntries

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic SecondOrderProgramListCode
open SecondOrderProgramListFold SecondOrderProgramListShift GraphSyntax PrimitiveFormulas
open SecondOrderProgramListReverse
open SecondOrderProgramListMap
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLength (length_zero_l)
open SecondOrderProgramListIteration (iterate_m)
open SecondOrderProgramListLookup (lookup_m)
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-! ## 内部端：真实公式的广义累计器长度不变量（嵌套状态） -/

/-- 广义累计器折叠长度不变量的实际公式。自由槽 `[a, F, L, E]`（`a` 为归纳列表码，`F` 为
`fold (map_step c)` 折叠图，`L` 为长度图，`E` 为实际累计读取图 `graph_m map_extract_m`
（`.comp .right .right`），把状态 `pair p (pair i acc)` 解到内层累计码 `acc`）；正文从外到内
绑定 `[v, y, n, m, va, ya]`：`F(a, v)→y → E(v, va) → L(a, n) → L(va, m) → E(y, ya) →
L(ya, add n m)`。即折叠 `n` 个内部头项后，输出状态的内层累计码恰比初始内层累计码多 `n` 项，
与随状态携带的参数 `p`、当前下标 `i` 无关。只用嵌套 `.imp`（不合取），使语义桥以
`simp only + rfl` 闭合。配对读取一律走 `output_m`／`edge_m` 原关系，不含非纯的 `.pair` 项。 -/
def entries_length_m : Formula signature_m [] [.num, .set, .set, .set] :=
  .forallE .num (.forallE .num (.forallE .num (.forallE .num (.forallE .num (.forallE .num
    (.imp
      (output_m (.fvar (.there .here)) (.fvar .here)
        (.bvar (.there (.there (.there (.there (.there .here))))))
        (.bvar (.there (.there (.there (.there .here))))))
      (.imp
        (edge_m (.fvar (.there (.there (.there .here))))
          (.bvar (.there (.there (.there (.there (.there .here))))))
          (.bvar (.there .here)))
        (.imp
          (edge_m (.fvar (.there (.there .here))) (.fvar .here)
            (.bvar (.there (.there (.there .here)))))
          (.imp
            (edge_m (.fvar (.there (.there .here)))
              (.bvar (.there .here))
              (.bvar (.there (.there .here))))
            (.imp
              (edge_m (.fvar (.there (.there (.there .here))))
                (.bvar (.there (.there (.there (.there .here)))))
                (.bvar .here))
              (edge_m (.fvar (.there (.there .here)))
                (.bvar .here)
                (Term.app (σ := signature_m) .add
                  (.cons (.bvar (.there (.there (.there .here))))
                    (.cons (.bvar (.there (.there .here))) .nil))))))))))))))

/-- 长度不变量公式属于原纯算术语言。 -/
theorem entries_length_language_m : language_m entries_length_m = true :=
  pure_language_m _ rfl

/-- 实际公式在模型中的真值即广义累计器长度不变量：自由变量按 `a, F, L, E` 送入环境，
六个内层量化变量按 `v, y, n, m, va, ya` 从外到内绑定，逐段 `simp only` 展开 `output_m`／
`edge_m` 到 `relation_l` 与 `add_l`。 -/
theorem entries_length_syntax_l (F L E : set_l ℳ) (a : num_l ℳ) :
    Formula.satisfies
      (((((Env.empty (M := ℳ)).pushFree E).pushFree L).pushFree F).pushFree a)
      entries_length_m ↔
      ∀ v y n m va ya : num_l ℳ, relation_l F (value_l a v) y → relation_l E v va →
        relation_l L a n → relation_l L va m → relation_l E y ya →
          relation_l L ya (add_l n m) := by
  simp only [entries_length_m, Formula.satisfies, output_syntax_l, SecondOrderPairing.edge_l]
  rfl

/-- 广义累计器折叠保持内层累计长度：对任意完整状态 `v`，若 `F(a, v)→y`、`E(v)=va`、源码
`a` 长 `n`、`va` 长 `m`、`E(y)=ya`，则 `ya` 长 `add n m`。对内部列表码 `a` 用真实公式
`entries_length_m` 作原列表归纳（`SecondOrderListInduction.list_induct_l`）。

空码基：`fold_zero_l` 给出 `v = y`，故 `E(y) = E(v)`（提取图函数性）即 `ya = va`；源码 `0`
长 `0`（`length_zero_l` + 函数唯一）使 `add n m = m`，目标归约为已知 `L va m`。

cons 步：`fold_cons_l` 把 `F(succ(pair a t), v)→y` 拆成 `S(v, a)→w` 与 `F(t, w)→y`；先把任意
状态 `v` 用 `SecondOrderUnpairing.surjective_l` 两次拆成 `pair p (pair i A)`，由
`map_extract_rel_l` 得 `A = va`，再用真实一步 `map_step_rel_l` 把 `w` 表为
`pair p (pair (succ i) (succ (value mc va)))`。提取图给出 `E(w) = succ (value mc va)`，
`length_cons_l` 给出其长度 `succ m`；`length_cons_l` 把源码长度 `n` 拆成 `succ nt` 与 `L t nt`。
归纳假设在状态 `w` 上得 `L ya (add nt (succ m))`，再用 `succ_add`/`add_succ` 归到
`L ya (add (succ nt) m)`。全程只用真实图与 `length_*`/`map_*`/`fold_*` 已验引理，不假设内部
长度标准，不收集外谓词。 -/
theorem fold_length_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {C F L E I : set_l ℳ}
    (hC : graph_semantics_l (graph_m c) C)
    (hF : graph_semantics_l (graph_m (fold_m (map_step_m c))) F)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m map_extract_m) E)
    (hI : graph_semantics_l (graph_m iterate_m) I) :
    ∀ a : num_l ℳ, ∀ v y n m va ya : num_l ℳ, relation_l F (value_l a v) y →
      relation_l E v va → relation_l L a n → relation_l L va m → relation_l E y ya →
        relation_l L ya (add_l n m) := by
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ (map_step_m c)
  let hLf := function_of_semantics_l hℳ length_m hL
  let hEf := function_of_semantics_l hℳ map_extract_m hE
  have h00 : relation_l L (zero_l ℳ) (zero_l ℳ) :=
    (SecondOrderProgramLength.length_rel_l hℳ hL hI (zero_l ℳ) (zero_l ℳ)).mpr
      ((length_zero_l hℳ hI (zero_l ℳ)).mpr rfl)
  refine SecondOrderListInduction.list_induct_l hℳ entries_length_m
    entries_length_language_m
    ((((Env.empty (M := ℳ)).pushFree E).pushFree L).pushFree F)
    (fun a => ∀ v y n m va ya : num_l ℳ, relation_l F (value_l a v) y →
      relation_l E v va → relation_l L a n → relation_l L va m → relation_l E y ya →
        relation_l L ya (add_l n m))
    (fun a => entries_length_syntax_l F L E a) ?_ ?_
  · -- 空码：v = y 使两侧提取相同，源码长度 n = 0，故 add 0 m = m。
    intro v y n m va ya hy hEva hla hlva hEya
    have hv : v = y := (fold_zero_l hℳ (map_step_m c) hF v y).mp hy
    have hn : n = zero_l ℳ := function_value_unique_l hLf hla h00
    rw [← hv] at hEya
    have hyava : ya = va := function_value_unique_l hEf hEya hEva
    subst hn
    rw [SecondOrderNumbers.zero_add_l hℳ m, hyava]
    exact hlva
  · -- cons 码：先拆任意状态 v = pair p (pair i va)，真实一步推进 w，长度逐项累加。
    intro a t ih v y n m va ya hy hEva hla hlva hEya
    rw [fold_cons_l hℳ (map_step_m c) hF hS a t v y] at hy
    obtain ⟨w, hsw, htw⟩ := hy
    obtain ⟨p, s, rfl⟩ := SecondOrderUnpairing.surjective_l hℳ v
    obtain ⟨i, A, rfl⟩ := SecondOrderUnpairing.surjective_l hℳ s
    have hAv : A = va := (map_extract_rel_l hℳ hE p i A va).mp hEva
    rw [hAv] at hsw
    obtain ⟨mc, _, hw⟩ := (map_step_rel_l hℳ c hC hS p i va a w).mp hsw
    have hEw : relation_l E w (succ_l (value_l mc va)) := by
      rw [← hw]
      exact (map_extract_rel_l hℳ hE p (succ_l i) (succ_l (value_l mc va))
        (succ_l (value_l mc va))).mpr rfl
    have hLvwa : relation_l L (succ_l (value_l mc va)) (succ_l m) :=
      (SecondOrderProgramLength.length_rel_l hℳ hL hI
        (succ_l (value_l mc va)) (succ_l m)).mpr
        ((length_cons_l hℳ hI mc va m).mpr
          ((SecondOrderProgramLength.length_rel_l hℳ hL hI va m).mp hlva))
    have hnz : succ_l (value_l a t) ≠ zero_l ℳ := nonzero_l hℳ (value_l a t)
    have hspec :=
      (SecondOrderProgramLength.length_rel_l hℳ hL hI (succ_l (value_l a t)) n).mp hla
    rcases predecessor_l hℳ n with rfl | ⟨nt, rfl⟩
    · exact absurd ((length_zero_l hℳ hI (succ_l (value_l a t))).mp hspec) hnz
    · have hlt : relation_l L t nt :=
          (SecondOrderProgramLength.length_rel_l hℳ hL hI t nt).mpr
            ((length_cons_l hℳ hI a t nt).mp hspec)
      have hi := ih w y nt (succ_l m) (succ_l (value_l mc va)) ya htw hEw hlt hLvwa hEya
      rw [SecondOrderNumbers.succ_add_l hℳ nt m, ← add_succ_l hℳ nt m]
      exact hi

/-! ## 公理审计

本模块公共声明仅允许既有标准公理集合（propext/Quot.sound/Classical.choice），无新增公理，
亦不得有 `sorryAx`。审计置于命名空间内、`end` 之前。 -/

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListMapEntries
