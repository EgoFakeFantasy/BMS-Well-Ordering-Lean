import BMSConstructibleBridge.SecondOrderProgramListMapIndices
import BMSConstructibleBridge.SecondOrderProgramListMapEntries
import BMSConstructibleBridge.SecondOrderProgramListMap
import BMSConstructibleBridge.SecondOrderProgramLength
import BMSConstructibleBridge.SecondOrderProgramListLookup
import BMSConstructibleBridge.SecondOrderListInduction

/-!
# 任务34 阶段C cp2：带参数 mapIdx 折叠的前段倒序回调下标

阶段C cp1（`SecondOrderProgramListMapIndices`，SHA `85832B12…` 已 #1790 验收冻结）给出后
`m` 项保序的逐内部下标闭环。本模块补上前 `n` 项：`fold (map_step c)` 每消费一个头项 `a`，
在回调图 `C` 上取值 `mc = C(pair p (pair ii a))` 并把状态更新为
`pair p (pair (succ ii) (succ (value mc acc)))`，新回调值总是压到累计码表首，故折叠 `n` 项后
输出累计码 `ya` 的前 `n` 项**倒序**排列回调值：位置 `j`（见证 `succ j + k = n`）上的值等于
`C(pair p (pair (add ii k) a[k]))`——参数 `p`、起始下标 `ii`、内部界与存在回调值全部保留，
回调一律走实际图 `C`（`graph_m c`），不以某个主机函数值定义替代。

配对码在纯语言内不引入 `.pair` 项：状态分解假设 `z = ⟨ii, va⟩`、`v = ⟨p, z⟩` 与回调输入码
`u = ⟨ii + k, e⟩` 都用算术两分支图 `PrimitiveFormulas.pair_m` 表达，语义桥经
`SecondOrderPairing.formula_l` 归约为 `value_l` 等式；`C(⟨p, u⟩)=w` 即 `output_m C p u w`。

归纳仍用真实公式 `entries_front_m` 在内部列表码上走 `SecondOrderListInduction.list_induct_l`
（#1776 门：归纳器环境只送到最外层自由槽，不含归纳槽 `a`）。空码基由 `succ j + k = 0` 矛盾；
cons 步按 `k` 分派：`k = succ kp` 交给归纳假设并用 `lookup_cons_succ_l` 对齐源码后继位读取；
`k = 0`（即位置 `j = nt`，输出前段末位）不被归纳假设覆盖——该位恰是最先消费的头码的回调值
`mc`，由 cp1 已冻后段定理 `fold_back_l` 在递归状态上取内部下标 `0` 给出
`K(ya, nt) = K(succ(value mc va), 0) = mc`，两侧再用 `lookup_cons_zero_l` 与头码读取归约到
`C(pair p (pair ii a)) = w`（右到左用 `C` 图函数性收拢，左到右直接取回调方程）。

把 `extract ∘ fold ∘ call` 归约到零初值、得到 `map_m c` 逐内部下标规格留待下一检查点；
本文件不触碰 cp1、阶段A/B 与反转模块的任何冻结资源，不假设内部长度标准、不收集外谓词、
图参数一律取实际 `graph_m`，越界补零（`lookup_past_end_l`）不进入结论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListMapFront

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

/-! ## 内部端：真实公式的前段倒序回调不变量（嵌套状态） -/

/-- 前 `n` 项倒序携带回调值不变量的实际公式。自由槽 `[a, F, L, E, K, C]`（`a` 为归纳列表码，
`F` 为 `fold (map_step c)` 折叠图，`L` 为长度图，`E` 为累计提取图 `graph_m map_extract_m`，
`K` 为按位读取图 `graph_m lookup_m`，`C` 为实际回调图 `graph_m c`）；正文从外到内绑定
`[v, y, n, m, va, ya, p, ii, z, j, k, w]`：
`F(a, v)→y → E(v)→va → L(a)→n → L(va)→m → E(y)→ya → z=⟨ii,va⟩ → v=⟨p,z⟩ →
succ j + k = n → (K(ya, j)→w ↔ ∃ e u, K(a, k)→e ∧ u=⟨ii+k, e⟩ ∧ C(⟨p,u⟩)→w)`。
前件只用嵌套 `.imp`，末段 `.conj` 两个 `.imp` 表达 `↔`；配对码全部走纯算术图 `pair_m`，
不含非纯的 `.pair` 项，语义桥以 `simp only + rfl` 闭合。 -/
def entries_front_m : Formula signature_m [] [.num, .set, .set, .set, .set, .set] :=
  (.forallE .num
    (.forallE .num
      (.forallE .num
        (.forallE .num
          (.forallE .num
            (.forallE .num
              (.forallE .num
                (.forallE .num
                  (.forallE .num
                    (.forallE .num
                      (.forallE .num
                        (.forallE .num
                          (.imp
                            (output_m (.fvar (.there .here)) (.fvar .here) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))
                            (.imp
                              (edge_m (.fvar (.there (.there (.there .here)))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there .here)))))))))
                              (.imp
                                (edge_m (.fvar (.there (.there .here))) (.fvar .here) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
                                (.imp
                                  (edge_m (.fvar (.there (.there .here))) (.bvar (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
                                  (.imp
                                    (edge_m (.fvar (.there (.there (.there .here)))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.bvar (.there (.there (.there (.there (.there (.there .here))))))))
                                    (.imp
                                      (PrimitiveFormulas.pair_m (.bvar (.there (.there (.there (.there .here))))) (.bvar (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.bvar (.there (.there (.there .here)))))
                                      (.imp
                                        (PrimitiveFormulas.pair_m (.bvar (.there (.there (.there (.there (.there .here)))))) (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))
                                        (.imp
                                          (.equal (Term.app (σ := signature_m) .add (.cons (Term.app (σ := signature_m) .succ (.cons (.bvar (.there (.there .here))) .nil)) (.cons (.bvar (.there .here)) .nil))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
                                          (.conj
                                            (.imp
                                              (output_m (.fvar (.there (.there (.there (.there .here))))) (.bvar (.there (.there (.there (.there (.there (.there .here))))))) (.bvar (.there (.there .here))) (.bvar .here))
                                              (.existsE .num
                                                (.existsE .num
                                                  (.conj
                                                    (output_m (.fvar (.there (.there (.there (.there .here))))) (.fvar .here) (.bvar (.there (.there (.there .here)))) (.bvar (.there .here)))
                                                    (.conj
                                                      (PrimitiveFormulas.pair_m (Term.app (σ := signature_m) .add (.cons (.bvar (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.bvar (.there (.there (.there .here)))) .nil))) (.bvar (.there .here)) (.bvar .here))
                                                      (output_m (.fvar (.there (.there (.there (.there (.there .here)))))) (.bvar (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.bvar .here) (.bvar (.there (.there .here)))))))))
                                            (.imp
                                              (.existsE .num
                                                (.existsE .num
                                                  (.conj
                                                    (output_m (.fvar (.there (.there (.there (.there .here))))) (.fvar .here) (.bvar (.there (.there (.there .here)))) (.bvar (.there .here)))
                                                    (.conj
                                                      (PrimitiveFormulas.pair_m (Term.app (σ := signature_m) .add (.cons (.bvar (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.bvar (.there (.there (.there .here)))) .nil))) (.bvar (.there .here)) (.bvar .here))
                                                      (output_m (.fvar (.there (.there (.there (.there (.there .here)))))) (.bvar (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.bvar .here) (.bvar (.there (.there .here))))))))
                                              (output_m (.fvar (.there (.there (.there (.there .here))))) (.bvar (.there (.there (.there (.there (.there (.there .here))))))) (.bvar (.there (.there .here))) (.bvar .here))))))))))))))))))))))))

/-- 前段不变量公式属于原纯算术语言：`pair_m` 只引入 add/mul 与 `.equal` 项，无 `.pair` 项。 -/
theorem entries_front_language_m : language_m entries_front_m = true := pure_language_m _ rfl

/-- 实际公式在模型中的真值即前 `n` 项倒序回调不变量：自由变量按 `a, F, L, E, K, C` 送入环境，
十二个内层量化变量按 `v, y, n, m, va, ya, p, ii, z, j, k, w` 从外到内绑定；`pair_m` 经
`SecondOrderPairing.formula_l` 归约为 `value_l` 等式，末段两个存在量词读取为 `∃ e u`。 -/
theorem entries_front_syntax_l (F L E K C : set_l ℳ) (a : num_l ℳ) :
    Formula.satisfies (((((((Env.empty (M := ℳ)).pushFree C).pushFree K).pushFree E).pushFree L).pushFree F).pushFree a)
      entries_front_m ↔
      ∀ v y n m va ya p ii z j k w : num_l ℳ, relation_l F (value_l a v) y → relation_l E v va →
        relation_l L a n → relation_l L va m → relation_l E y ya → value_l ii va = z →
          value_l p z = v → add_l (succ_l j) k = n →
            (relation_l K (value_l ya j) w ↔
              ∃ e u : num_l ℳ, relation_l K (value_l a k) e ∧ value_l (add_l ii k) e = u ∧
                relation_l C (value_l p u) w) := by
  simp only [entries_front_m, Formula.satisfies, output_syntax_l, SecondOrderPairing.edge_l,
    SecondOrderPairing.formula_l, ←iff_def]
  rfl

/-- 广义累计器折叠的前 `n` 项倒序携带回调值：源码 `a` 长 `n`、状态 `v = pair p (pair ii va)`、
`va` 长 `m`、输出提取 `ya` 时，内部位置 `j`（见证 `succ j + k = n`）的读取值等于回调值
`C (pair p (pair (add ii k) a[k]))`，其中 `a[k]` 由同一读取图 `K` 给出。对内部列表码 `a` 用
真实公式 `entries_front_m` 作原列表归纳。

空码基：`succ j + k = 0` 矛盾（后继和不为零）。cons 步：`fold_cons_l` 拆折叠为真实一步
`S(v, a)→st` 与 `F(t, st)→y`；用状态分解假设把 `v` 写成 `pair p (pair ii va)`，
`map_step_rel_l` 给出 `st = pair p (pair (succ ii) (succ (value mc va)))` 与回调方程
`C(pair p (pair ii a)) = mc`，`map_extract_rel_l`／`length_cons_l` 给出新状态的提取与长度。
按 `k` 分派：`k = succ kp` 时归纳假设在 `st` 上把界化为 `succ j + kp = nt`，配对码经
`add_succ_l`／`succ_add_l` 重排，源码后继位读取用 `lookup_cons_succ_l` 双向对齐；`k = 0`
时 `succ j = succ nt` 给出 `j = nt`，输出前段末位由已冻 `fold_back_l`（内部下标 `0`，界
`zero_succ_l`）归约到 `K(succ (value mc va), 0)`，两侧再经 `lookup_cons_zero_l` 收成
`mc = w` 与 `C(pair p (pair ii a)) = w`（右到左用 `C` 图函数性收拢，左到右直接取回调方程）。
全程不假设内部长度标准，不以主机函数值替代实际 `C` 图。 -/
theorem fold_front_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {C F L E K I : set_l ℳ}
    (hC : graph_semantics_l (graph_m c) C)
    (hF : graph_semantics_l (graph_m (fold_m (map_step_m c))) F)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m map_extract_m) E)
    (hK : graph_semantics_l (graph_m lookup_m) K)
    (hI : graph_semantics_l (graph_m iterate_m) I) :
    ∀ a : num_l ℳ, ∀ v y n m va ya p ii z j k w : num_l ℳ,
      relation_l F (value_l a v) y → relation_l E v va → relation_l L a n →
        relation_l L va m → relation_l E y ya → value_l ii va = z → value_l p z = v →
          add_l (succ_l j) k = n →
            (relation_l K (value_l ya j) w ↔
              ∃ e u : num_l ℳ, relation_l K (value_l a k) e ∧ value_l (add_l ii k) e = u ∧
                relation_l C (value_l p u) w) := by
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ (map_step_m c)
  let hLf := function_of_semantics_l hℳ length_m hL
  let hCf := function_of_semantics_l hℳ c hC
  have h00 : relation_l L (zero_l ℳ) (zero_l ℳ) :=
    (SecondOrderProgramLength.length_rel_l hℳ hL hI (zero_l ℳ) (zero_l ℳ)).mpr
      ((length_zero_l hℳ hI (zero_l ℳ)).mpr rfl)
  refine SecondOrderListInduction.list_induct_l hℳ entries_front_m
    entries_front_language_m
    ((((((Env.empty (M := ℳ)).pushFree C).pushFree K).pushFree E).pushFree L).pushFree F)
    (fun a => ∀ v y n m va ya p ii z j k w : num_l ℳ,
      relation_l F (value_l a v) y → relation_l E v va → relation_l L a n →
        relation_l L va m → relation_l E y ya → value_l ii va = z → value_l p z = v →
          add_l (succ_l j) k = n →
            (relation_l K (value_l ya j) w ↔
              ∃ e u : num_l ℳ, relation_l K (value_l a k) e ∧ value_l (add_l ii k) e = u ∧
                relation_l C (value_l p u) w))
    (fun a => entries_front_syntax_l F L E K C a) ?_ ?_
  · -- 空码：n = 0 使 succ j + k = 0 矛盾。
    intro _ _ n _ _ _ _ _ _ j k _ _ _ hla _ _ _ _ hjk
    have hn : n = zero_l ℳ := function_value_unique_l hLf hla h00
    subst hn
    rw [SecondOrderNumbers.succ_add_l hℳ j k] at hjk
    exact absurd hjk (nonzero_l hℳ (add_l j k))
  · -- cons 码：拆状态、真实一步推进 st，再按 k 分派。
    intro a t ih v y n m va ya p ii z j k w hf _ hla hlva hEya hz hv hjk
    rw [fold_cons_l hℳ (map_step_m c) hF hS a t v y] at hf
    obtain ⟨st, hsw, htw⟩ := hf
    rw [← hz] at hv
    rw [← hv] at hsw
    obtain ⟨mcb, hcm, hst⟩ := (map_step_rel_l hℳ c hC hS p ii va a st).mp hsw
    have hEst : relation_l E st (succ_l (value_l mcb va)) := by
      rw [← hst]
      exact (map_extract_rel_l hℳ hE p (succ_l ii) (succ_l (value_l mcb va))
        (succ_l (value_l mcb va))).mpr rfl
    have hLsw : relation_l L (succ_l (value_l mcb va)) (succ_l m) :=
      (SecondOrderProgramLength.length_rel_l hℳ hL hI
        (succ_l (value_l mcb va)) (succ_l m)).mpr
        ((length_cons_l hℳ hI mcb va m).mpr
          ((SecondOrderProgramLength.length_rel_l hℳ hL hI va m).mp hlva))
    have hnz : succ_l (value_l a t) ≠ zero_l ℳ := nonzero_l hℳ (value_l a t)
    have hspec :=
      (SecondOrderProgramLength.length_rel_l hℳ hL hI (succ_l (value_l a t)) n).mp hla
    rcases predecessor_l hℳ n with rfl | ⟨nt, rfl⟩
    · exact absurd ((length_zero_l hℳ hI (succ_l (value_l a t))).mp hspec) hnz
    · have hlt : relation_l L t nt :=
          (SecondOrderProgramLength.length_rel_l hℳ hL hI t nt).mpr
            ((length_cons_l hℳ hI a t nt).mp hspec)
      rcases predecessor_l hℳ k with rfl | ⟨kp, rfl⟩
      · -- k = 0：j = nt 是输出前段末位，由已冻后段定理在内部下标 0 处补齐。
        have hsuccj : succ_l j = succ_l nt := by
          rw [← add_zero_l hℳ (succ_l j)]
          exact hjk
        have hj : j = nt := ((injective_l hℳ).eq_iff).mp hsuccj
        have hb := SecondOrderProgramListMapIndices.fold_back_l hℳ c hC hF hL hE hK hI
          t st y nt (succ_l m) (succ_l (value_l mcb va)) ya (zero_l ℳ) w
          htw hEst hlt hLsw hEya (SecondOrderOrder.zero_succ_l hℳ m)
        have h1 : relation_l K (value_l ya nt) w ↔ mcb = w := by
          rw [← add_zero_l hℳ nt]
          exact hb.trans (SecondOrderProgramListLookup.lookup_cons_zero_l hℳ hK mcb va w)
        rw [hj]
        constructor
        · intro hx
          have hw := h1.mp hx
          refine ⟨a, value_l ii a,
            (SecondOrderProgramListLookup.lookup_cons_zero_l hℳ hK a t a).mpr rfl, ?_, ?_⟩
          · rw [add_zero_l hℳ ii]
          · rw [← hw]
            exact hcm
        · rintro ⟨e, u, he, hru, hCu⟩
          have hea : a = e :=
            (SecondOrderProgramListLookup.lookup_cons_zero_l hℳ hK a t e).mp he
          rw [add_zero_l hℳ ii] at hru
          rw [← hru, ← hea] at hCu
          have hw : mcb = w := (function_value_unique_l hCf hCu hcm).symm
          exact h1.mpr hw
      · -- k = succ kp：归纳假设归约到 t 的 kp 位，两侧读取与配对码逐项对齐。
        have hsucc : succ_l (add_l (succ_l j) kp) = succ_l nt := by
          rw [← add_succ_l hℳ (succ_l j) kp]
          exact hjk
        have hjn : add_l (succ_l j) kp = nt := ((injective_l hℳ).eq_iff).mp hsucc
        have hi := ih st y nt (succ_l m) (succ_l (value_l mcb va)) ya p (succ_l ii)
          (value_l (succ_l ii) (succ_l (value_l mcb va))) j kp w
          htw hEst hlt hLsw hEya rfl hst hjn
        refine ⟨fun hx => ?_, fun hy => ?_⟩
        · obtain ⟨e, u, he, hru, hCu⟩ := hi.mp hx
          rw [SecondOrderNumbers.succ_add_l hℳ ii kp, ← add_succ_l hℳ ii kp] at hru
          exact ⟨e, u, (SecondOrderProgramListLookup.lookup_cons_succ_l hℳ hK a t kp e).mpr he,
            hru, hCu⟩
        · obtain ⟨e, u, he, hru, hCu⟩ := hy
          rw [add_succ_l hℳ ii kp, ← SecondOrderNumbers.succ_add_l hℳ ii kp] at hru
          exact hi.mpr ⟨e, u,
            (SecondOrderProgramListLookup.lookup_cons_succ_l hℳ hK a t kp e).mp he, hru, hCu⟩

/-! ## 公理审计

本模块公共声明仅允许既有标准公理集合（propext/Quot.sound/Classical.choice），无新增公理，
亦不得有 `sorryAx`。审计置于命名空间内、`end` 之前。 -/

#print axioms entries_front_m
#print axioms entries_front_language_m
#print axioms entries_front_syntax_l
#print axioms fold_front_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListMapFront
