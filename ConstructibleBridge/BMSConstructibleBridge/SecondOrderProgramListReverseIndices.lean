import BMSConstructibleBridge.SecondOrderProgramListReverseEntries
import BMSConstructibleBridge.SecondOrderProgramListLookup

/-!
# 任务33 阶段C：反转折叠逐内部下标对应

阶段B（`SecondOrderProgramListReverseEntries`）已在任意 Z₂ 模型中证明广义累计器折叠
`F` 保持长度：源列表码 `a` 长 `n`、累计码 `v` 长 `m` 时折叠输出 `y` 长 `add n m`。
本模块把该长度保持升级为逐内部下标条目对应。折叠的 cons 递推（`reverse_fold_cons_l`）
把累计值从 `v` 更新为 `succ (value a v)`，因此与阶段B 相同，归纳不变量对累计码全称量化。

设 `y = fold (reverse_step) (pair a v)`。标准端有 `y = reverse a ++ v`，故：
- 后 `m` 项保序：对内部下标 `i < m`，`lookup y (add n i) = lookup v i`；
- 前 `n` 项倒序：对内部下标 `j`、见证 `k` 满足 `succ j + k = n`，`lookup y j = lookup a k`。

两个结论各自在原列表码上用真实公式 `entries_back_m`／`entries_front_m` 作
`SecondOrderListInduction.list_induct_l` 归纳。前项结论的 `k = 0`（即头码 `a` 落在输出
末前位）单靠前项归纳假设不足，需先已证的后项定理在该递归调用上给出该位等于 `a`。
最后把前项结论特化到零初值累计码，得到 `reverse_m` 在任意内部合法下标处输出源逆序项。

不假设内部长度标准，不把任意外部谓词收集为模型集合，图参数一律取实际 `graph_m`；
下标越界的补零（`lookup_past_end_l`）不进入任一结论，界全部由 `succ j + k = n`／
`SecondOrderOrder.lt_l` 的真实公式见证给出。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListReverseIndices

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic SecondOrderProgramListCode
open SecondOrderProgramListFold SecondOrderProgramListShift GraphSyntax PrimitiveFormulas
open SecondOrderProgramListReverse SecondOrderProgramListReverseEntries
open SecondOrderOrder (lt_l)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLength (length_zero_l)
open SecondOrderProgramListIteration (iterate_m)
open SecondOrderProgramListLookup (lookup_m lookup_cons_zero_l lookup_cons_succ_l)
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-! ## 内部端：真实公式的广义累计器后段下标不变量 -/

/-- 后 `m` 项保序不变量的实际公式。自由槽 `[a, F, L, E]`（`a` 为归纳列表码，`F` 折叠图、
`L` 长度图、`E` 读取图）；正文从外到内绑定 `[v, y, n, m, i, w]`：
`F(a, v)→y → L(a, n) → L(v, m) → i < m → (E(y, n + i)→w ↔ E(v, i)→w)`。 -/
def entries_back_m : Formula signature_m [] [.num, .set, .set, .set] :=
(.forallE .num
  (.forallE .num
    (.forallE .num
      (.forallE .num
        (.forallE .num
          (.forallE .num
            (.imp
              (.conj
                (.conj
                  (.conj
                    (output_m (.fvar (.there .here)) (.fvar .here) (.bvar (.there (.there (.there (.there (.there .here)))))) (.bvar (.there (.there (.there (.there .here))))))
                    (edge_m (.fvar (.there (.there .here))) (.fvar .here) (.bvar (.there (.there (.there .here))))))
                  (edge_m (.fvar (.there (.there .here))) (.bvar (.there (.there (.there (.there (.there .here)))))) (.bvar (.there (.there .here)))))
                (PrimitiveFormulas.lt_m (.bvar (.there .here)) (.bvar (.there (.there .here)))))
              (.conj
                (.imp
                  (output_m (.fvar (.there (.there (.there .here)))) (.bvar (.there (.there (.there (.there .here)))))
                    (Term.app (σ := signature_m) .add (.cons (.bvar (.there (.there (.there .here)))) (.cons (.bvar (.there .here)) .nil))) (.bvar .here))
                  (output_m (.fvar (.there (.there (.there .here)))) (.bvar (.there (.there (.there (.there (.there .here)))))) (.bvar (.there .here)) (.bvar .here)))
                (.imp
                  (output_m (.fvar (.there (.there (.there .here)))) (.bvar (.there (.there (.there (.there (.there .here)))))) (.bvar (.there .here)) (.bvar .here))
                  (output_m (.fvar (.there (.there (.there .here)))) (.bvar (.there (.there (.there (.there .here)))))
                    (Term.app (σ := signature_m) .add (.cons (.bvar (.there (.there (.there .here)))) (.cons (.bvar (.there .here)) .nil))) (.bvar .here)))))))))))

/-- 后段下标不变量公式属于原纯算术语言。 -/
theorem entries_back_language_m : language_m entries_back_m = true := pure_language_m _ rfl

/-- 实际公式在模型中的真值即后 `m` 项保序不变量。 -/
theorem entries_back_syntax_l (F L E : set_l ℳ) (a : num_l ℳ) :
    Formula.satisfies (((((Env.empty (M := ℳ)).pushFree E).pushFree L).pushFree F).pushFree a)
      entries_back_m ↔
      ∀ v y n m i w : num_l ℳ, relation_l F (value_l a v) y → relation_l L a n →
        relation_l L v m → SecondOrderOrder.lt_l i m →
          (relation_l E (value_l y (add_l n i)) w ↔ relation_l E (value_l v i) w) := by
  simp only [entries_back_m, Formula.satisfies, output_syntax_l, SecondOrderPairing.edge_l,
    SecondOrderOrder.formula_l, and_imp, ←iff_def]
  rfl

/-- 广义累计器折叠的后 `m` 项保持累计原顺序：源长 `n` 时，输出的内部位置 `add n i`
（`i < m`）读取值与累计码位置 `i` 相同。对内部列表码 `a` 用真实公式 `entries_back_m` 作
原列表归纳。空码基：折叠保持累计值（`y = v`）且 `n = 0`，故 `add 0 i = i` 两侧同读。
cons 步：折叠递推把累计更新为 `succ (value a v)`，长度 `n = succ n_t`、`m' = succ m`；
把内部下标 `add (succ n_t) i = add n_t (succ i)` 交给归纳假设在 `succ i < succ m` 下使用，
再用 `lookup_cons_succ_l` 把 `succ (value a v)` 的后继位归约回 `v` 的 `i` 位。全程以真实
`lt_l` 见证界，不触碰越界补零。 -/
theorem fold_back_l (hℳ : Theory.Models ℳ theory_m) {F L E I : set_l ℳ}
    (hF : graph_semantics_l (graph_m (fold_m reverse_step_m)) F)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hI : graph_semantics_l (graph_m iterate_m) I)
    (a v y n m i w : num_l ℳ) (hy : relation_l F (value_l a v) y)
    (hla : relation_l L a n) (hlv : relation_l L v m) (hit : SecondOrderOrder.lt_l i m) :
    relation_l E (value_l y (add_l n i)) w ↔ relation_l E (value_l v i) w := by
  obtain ⟨C, _, hC⟩ := graph_total_l hℳ reverse_step_m
  let hfun := function_of_semantics_l hℳ length_m hL
  have h00 : relation_l L (zero_l ℳ) (zero_l ℳ) :=
    (SecondOrderProgramLength.length_rel_l hℳ hL hI (zero_l ℳ) (zero_l ℳ)).mpr
      ((length_zero_l hℳ hI (zero_l ℳ)).mpr rfl)
  have key : ∀ x : num_l ℳ, ∀ v y n m i w : num_l ℳ, relation_l F (value_l x v) y →
      relation_l L x n → relation_l L v m → SecondOrderOrder.lt_l i m →
        (relation_l E (value_l y (add_l n i)) w ↔ relation_l E (value_l v i) w) := by
    refine SecondOrderListInduction.list_induct_l hℳ entries_back_m
      entries_back_language_m
      ((((Env.empty (M := ℳ)).pushFree E).pushFree L).pushFree F)
      (fun x => ∀ v y n m i w : num_l ℳ, relation_l F (value_l x v) y →
        relation_l L x n → relation_l L v m → SecondOrderOrder.lt_l i m →
          (relation_l E (value_l y (add_l n i)) w ↔ relation_l E (value_l v i) w))
      (fun x => entries_back_syntax_l F L E x) ?_ ?_
    · -- 空码：折叠保持累计值 y = v，源长 n = 0，故 add 0 i = i，两侧同读。
      intro v y n m i w hy hla hlv _
      have hyv : v = y := (reverse_fold_zero_l hℳ hF v y).mp hy
      have hn : n = zero_l ℳ := function_value_unique_l hfun hla h00
      subst hyv
      subst hn
      rw [SecondOrderNumbers.zero_add_l hℳ i]
    · -- cons 码：折叠递推更新累计为 succ (value a v)，把界 succ i < succ m 交给归纳假设。
      intro a t ih v y n m i w hy hla hlv hit
      rw [reverse_fold_cons_l hℳ hF hC] at hy
      have hnz : succ_l (value_l a t) ≠ zero_l ℳ := nonzero_l hℳ (value_l a t)
      have hspec :=
        (SecondOrderProgramLength.length_rel_l hℳ hL hI (succ_l (value_l a t)) n).mp hla
      rcases predecessor_l hℳ n with rfl | ⟨nt, rfl⟩
      · exact absurd ((length_zero_l hℳ hI (succ_l (value_l a t))).mp hspec) hnz
      · have hlt : relation_l L t nt :=
            (SecondOrderProgramLength.length_rel_l hℳ hL hI t nt).mpr
              ((length_cons_l hℳ hI a t nt).mp hspec)
        have hlc : relation_l L (succ_l (value_l a v)) (succ_l m) :=
          (SecondOrderProgramLength.length_rel_l hℳ hL hI
            (succ_l (value_l a v)) (succ_l m)).mpr
            ((length_cons_l hℳ hI a v m).mpr
              ((SecondOrderProgramLength.length_rel_l hℳ hL hI v m).mp hlv))
        have hit' : SecondOrderOrder.lt_l (succ_l i) (succ_l m) :=
          (SecondOrderOrder.succ_iff_l hℳ i m).mpr hit
        have hidx : add_l (succ_l nt) i = add_l nt (succ_l i) := by
          rw [SecondOrderNumbers.succ_add_l hℳ nt i, add_succ_l hℳ nt i]
        rw [hidx]
        exact (ih (succ_l (value_l a v)) y nt (succ_l m) (succ_l i) w hy hlt hlc hit').trans
          (lookup_cons_succ_l hℳ hE a v i w)
  exact key a v y n m i w hy hla hlv hit

/-! ## 内部端：真实公式的广义累计器前段倒序不变量 -/

/-- 前 `n` 项倒序不变量的实际公式。自由槽 `[a, F, L, E]`；正文从外到内绑定
`[v, y, n, m, j, k, w]`：`F(a, v)→y → L(a, n) → L(v, m) → succ j + k = n →
(E(y, j)→w ↔ E(a, k)→w)`。界 `j < n` 由见证方程 `succ j + k = n` 内建，无需独立 `lt`。 -/
def entries_front_m : Formula signature_m [] [.num, .set, .set, .set] :=
(.forallE .num
  (.forallE .num
    (.forallE .num
      (.forallE .num
        (.forallE .num
          (.forallE .num
            (.forallE .num
              (.imp
                (.conj
                  (.conj
                    (.conj
                      (output_m (.fvar (.there .here)) (.fvar .here) (.bvar (.there (.there (.there (.there (.there (.there .here))))))) (.bvar (.there (.there (.there (.there (.there .here)))))))
                      (edge_m (.fvar (.there (.there .here))) (.fvar .here) (.bvar (.there (.there (.there (.there .here)))))))
                    (edge_m (.fvar (.there (.there .here))) (.bvar (.there (.there (.there (.there (.there (.there .here))))))) (.bvar (.there (.there (.there .here))))))
                  (.equal
                    (Term.app (σ := signature_m) .add (.cons
                        (Term.app (σ := signature_m) .succ (.cons (.bvar (.there (.there .here))) .nil)) (.cons (.bvar (.there .here)) .nil))) (.bvar (.there (.there (.there (.there .here)))))))
                (.conj
                  (.imp
                    (output_m (.fvar (.there (.there (.there .here)))) (.bvar (.there (.there (.there (.there (.there .here)))))) (.bvar (.there (.there .here))) (.bvar .here))
                    (output_m (.fvar (.there (.there (.there .here)))) (.fvar .here) (.bvar (.there .here)) (.bvar .here)))
                  (.imp
                    (output_m (.fvar (.there (.there (.there .here)))) (.fvar .here) (.bvar (.there .here)) (.bvar .here))
                    (output_m (.fvar (.there (.there (.there .here)))) (.bvar (.there (.there (.there (.there (.there .here)))))) (.bvar (.there (.there .here))) (.bvar .here))))))))))))

/-- 前段倒序不变量公式属于原纯算术语言。 -/
theorem entries_front_language_m : language_m entries_front_m = true := pure_language_m _ rfl

/-- 实际公式在模型中的真值即前 `n` 项倒序不变量。 -/
theorem entries_front_syntax_l (F L E : set_l ℳ) (a : num_l ℳ) :
    Formula.satisfies (((((Env.empty (M := ℳ)).pushFree E).pushFree L).pushFree F).pushFree a)
      entries_front_m ↔
      ∀ v y n m j k w : num_l ℳ, relation_l F (value_l a v) y → relation_l L a n →
        relation_l L v m → add_l (succ_l j) k = n →
          (relation_l E (value_l y j) w ↔ relation_l E (value_l a k) w) := by
  simp only [entries_front_m, Formula.satisfies, output_syntax_l, SecondOrderPairing.edge_l,
    and_imp, ←iff_def]
  rfl

/-- 广义累计器折叠的前 `n` 项倒序对应源列表码：内部位置 `j`（见证 `succ j + k = n`）读取
输出值与源码位置 `k` 相同。对内部列表码 `a` 用真实公式 `entries_front_m` 作原列表归纳。
空码基：`n = 0` 使 `succ j + k = 0` 矛盾（后继和不为零）。cons 步：折叠递推更新累计为
`succ (value a v)`，`n = succ nt`。按 `k` 分派——`k = succ kp` 时 `succ j + kp = nt`，归纳
假设把 `E(y, j)` 归约到 `E(t, kp)`，`lookup_cons_succ_l` 把 `E(succ (value a t), succ kp)`
同样归约到 `E(t, kp)`；`k = 0` 时 `j = nt`，输出末前位恰是头码 `a`，此位不由前项归纳假设
覆盖，改由已证后段定理 `fold_back_l` 在递归调用（累计 `succ (value a v)`、界 `0 < succ m`）
给出，两侧再用 `lookup_cons_zero_l` 都归约到 `a = w`。 -/
theorem fold_front_l (hℳ : Theory.Models ℳ theory_m) {F L E I : set_l ℳ}
    (hF : graph_semantics_l (graph_m (fold_m reverse_step_m)) F)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hI : graph_semantics_l (graph_m iterate_m) I)
    (a v y n m j k w : num_l ℳ) (hy : relation_l F (value_l a v) y)
    (hla : relation_l L a n) (hlv : relation_l L v m) (hjk : add_l (succ_l j) k = n) :
    relation_l E (value_l y j) w ↔ relation_l E (value_l a k) w := by
  obtain ⟨C, _, hC⟩ := graph_total_l hℳ reverse_step_m
  let hfun := function_of_semantics_l hℳ length_m hL
  have h00 : relation_l L (zero_l ℳ) (zero_l ℳ) :=
    (SecondOrderProgramLength.length_rel_l hℳ hL hI (zero_l ℳ) (zero_l ℳ)).mpr
      ((length_zero_l hℳ hI (zero_l ℳ)).mpr rfl)
  have key : ∀ x : num_l ℳ, ∀ v y n m j k w : num_l ℳ, relation_l F (value_l x v) y →
      relation_l L x n → relation_l L v m → add_l (succ_l j) k = n →
        (relation_l E (value_l y j) w ↔ relation_l E (value_l x k) w) := by
    refine SecondOrderListInduction.list_induct_l hℳ entries_front_m
      entries_front_language_m
      ((((Env.empty (M := ℳ)).pushFree E).pushFree L).pushFree F)
      (fun x => ∀ v y n m j k w : num_l ℳ, relation_l F (value_l x v) y →
        relation_l L x n → relation_l L v m → add_l (succ_l j) k = n →
          (relation_l E (value_l y j) w ↔ relation_l E (value_l x k) w))
      (fun x => entries_front_syntax_l F L E x) ?_ ?_
    · -- 空码：n = 0 使 succ j + k = 0 矛盾。
      intro v y n m j k w hy hla hlv hjk
      have hn : n = zero_l ℳ := function_value_unique_l hfun hla h00
      subst hn
      rw [SecondOrderNumbers.succ_add_l hℳ j k] at hjk
      exact absurd hjk (nonzero_l hℳ (add_l j k))
    · -- cons 码：按 k 分派，k = 0 位由后段定理补齐。
      intro a t ih v y n m j k w hy hla hlv hjk
      rw [reverse_fold_cons_l hℳ hF hC] at hy
      have hnz : succ_l (value_l a t) ≠ zero_l ℳ := nonzero_l hℳ (value_l a t)
      have hspec :=
        (SecondOrderProgramLength.length_rel_l hℳ hL hI (succ_l (value_l a t)) n).mp hla
      rcases predecessor_l hℳ n with rfl | ⟨nt, rfl⟩
      · exact absurd ((length_zero_l hℳ hI (succ_l (value_l a t))).mp hspec) hnz
      · have hlt : relation_l L t nt :=
            (SecondOrderProgramLength.length_rel_l hℳ hL hI t nt).mpr
              ((length_cons_l hℳ hI a t nt).mp hspec)
        have hlc : relation_l L (succ_l (value_l a v)) (succ_l m) :=
          (SecondOrderProgramLength.length_rel_l hℳ hL hI
            (succ_l (value_l a v)) (succ_l m)).mpr
            ((length_cons_l hℳ hI a v m).mpr
              ((SecondOrderProgramLength.length_rel_l hℳ hL hI v m).mp hlv))
        rcases predecessor_l hℳ k with rfl | ⟨kp, rfl⟩
        · -- k = 0：j = nt，输出末前位 = 头码 a，两侧归约到 a = w。
          have hsuccj : succ_l j = succ_l nt := by
            rw [← add_zero_l hℳ (succ_l j)]
            exact hjk
          have hj : j = nt := ((injective_l hℳ).eq_iff).mp hsuccj
          have hb := fold_back_l hℳ hF hL hE hI t (succ_l (value_l a v)) y nt
            (succ_l m) (zero_l ℳ) w hy hlt hlc (SecondOrderOrder.zero_succ_l hℳ m)
          have h1 : relation_l E (value_l y nt) w ↔ a = w := by
            rw [← add_zero_l hℳ nt]
            exact hb.trans (lookup_cons_zero_l hℳ hE a v w)
          rw [hj]
          exact h1.trans (Iff.symm (lookup_cons_zero_l hℳ hE a t w))
        · -- k = succ kp：succ j + kp = nt，归纳假设与 lookup_cons_succ 都归约到 E(t, kp)。
          have hsucc : succ_l (add_l (succ_l j) kp) = succ_l nt := by
            rw [← add_succ_l hℳ (succ_l j) kp]
            exact hjk
          have hjn : add_l (succ_l j) kp = nt := ((injective_l hℳ).eq_iff).mp hsucc
          exact (ih (succ_l (value_l a v)) y nt (succ_l m) j kp w hy hlt hlc hjn).trans
            (Iff.symm (lookup_cons_succ_l hℳ hE a t kp w))
  exact key a v y n m j k w hy hla hlv hjk

/-! ## reverse 特化：任意内部合法下标输出逆序项 -/

/-- `reverse_m` 逐内部下标对应：源码 `a` 长 `n`、内部下标 `j` 及见证 `succ j + k = n` 时，
`reverse a` 的 `j` 位读取值等于源 `a` 的 `k` 位。经 `reverse_bridge_l` 把反转图归约为同一
折叠的零初值调用，再用前段倒序定理（累计长 `m = 0`，界 `succ j + k = n` 使 `j < n` 恒可
满足）得到。不引入标准性假设。 -/
theorem reverse_indices_l (hℳ : Theory.Models ℳ theory_m) {T F L E I : set_l ℳ}
    (hT : graph_semantics_l (graph_m reverse_m) T)
    (hF : graph_semantics_l (graph_m (fold_m reverse_step_m)) F)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hI : graph_semantics_l (graph_m iterate_m) I)
    (a y n j k w : num_l ℳ) (hay : relation_l T a y) (hla : relation_l L a n)
    (hjk : add_l (succ_l j) k = n) :
    relation_l E (value_l y j) w ↔ relation_l E (value_l a k) w := by
  have h00 : relation_l L (zero_l ℳ) (zero_l ℳ) :=
    (SecondOrderProgramLength.length_rel_l hℳ hL hI (zero_l ℳ) (zero_l ℳ)).mpr
      ((length_zero_l hℳ hI (zero_l ℳ)).mpr rfl)
  have hf := (reverse_bridge_l hℳ hT hF a y).mp hay
  exact fold_front_l hℳ hF hL hE hI a (zero_l ℳ) y n (zero_l ℳ) j k w hf hla h00 hjk

/-! ## 公理审计

本模块公共声明仅允许既有标准公理集合（propext/Quot.sound/Classical.choice），
无新增公理，亦不得有 `sorryAx`。审计置于命名空间内、`end` 之前。 -/

#print axioms entries_back_m
#print axioms entries_back_language_m
#print axioms entries_back_syntax_l
#print axioms fold_back_l
#print axioms entries_front_m
#print axioms entries_front_language_m
#print axioms entries_front_syntax_l
#print axioms fold_front_l
#print axioms reverse_indices_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListReverseIndices
