import BMSConstructibleBridge.SecondOrderProgramListReverse
import BMSConstructibleBridge.SecondOrderProgramLength
import BMSConstructibleBridge.SecondOrderProgramListLookup
import BMSConstructibleBridge.SecondOrderListInduction

/-!
# 任务33 阶段B：反转折叠广义累计器的内部长度保持

阶段A 已在原纯七构造上定义 `reverse_step_m = .comp .succ (.pair .right .left)` 与
`reverse_m = .comp (fold_m reverse_step_m) (.pair id .zero)`，并给出标准端
`fold reverse_step (pair (encode s) (encode t)) = encode (s.reverse ++ t)`。本模块把该
累积器反转升级为任意 Z₂ 模型中的内部规格。

折叠的 cons 递推把累计值从 `v` 更新为 `cons a v`，因此不能对固定累计值归纳；正确的
归纳不变量是对广义累计器陈述：从内部列表码 `a`、累计码 `v` 出发，折叠输出 `y` 满足
`length y = length a + length v`。本阶段先交付这一长度保持（阶段B第一层），随后再补
逐内部下标的反向对应（前 `n` 项逆序、后 `m` 项保序）。

全部内部结论通过真实公式 `entries_length_m` 的 AST、语言检查与语义对应，再用
`SecondOrderListInduction.list_induct_l` 在内部列表码上归纳得到。不假设内部长度标准，
不把任意外部谓词收集为模型集合，图参数一律取实际 `graph_m`。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListReverseEntries

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic SecondOrderProgramListCode
open SecondOrderProgramListFold SecondOrderProgramListShift GraphSyntax PrimitiveFormulas
open SecondOrderProgramListReverse
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLength (length_zero_l)
open SecondOrderProgramListIteration (iterate_m)
open SecondOrderProgramListLookup (lookup_m)
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-! ## 内部端：真实公式的广义累计器长度不变量 -/

/-- 广义累计器折叠长度不变量的实际公式。自由槽 `[a, F, L]`（`a` 为归纳列表码，
`F` 为折叠图，`L` 为长度图）；正文从内到外绑定 `[m, n, y, v]`：
`F(a, v)→y → L(a, n) → L(v, m) → L(y, n + m)`。 -/
def entries_length_m : Formula signature_m [] [.num, .set, .set] :=
  .forallE .num (.forallE .num (.forallE .num (.forallE .num
    (.imp
      (output_m (.fvar (.there .here)) (.fvar .here)
        (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here))))
      (.imp
        (edge_m (.fvar (.there (.there .here))) (.fvar .here) (.bvar (.there .here)))
        (.imp
          (edge_m (.fvar (.there (.there .here)))
            (.bvar (.there (.there (.there .here)))) (.bvar .here))
          (edge_m (.fvar (.there (.there .here))) (.bvar (.there (.there .here)))
            (Term.app (σ := signature_m) .add
              (.cons (.bvar (.there .here)) (.cons (.bvar .here) .nil))))))))))

/-- 长度不变量公式属于原纯算术语言。 -/
theorem entries_length_language_m : language_m entries_length_m = true :=
  pure_language_m _ rfl

/-- 实际公式在模型中的真值即广义累计器长度不变量。 -/
theorem entries_length_syntax_l (F L : set_l ℳ) (a : num_l ℳ) :
      Formula.satisfies ((((Env.empty (M := ℳ)).pushFree L).pushFree F).pushFree a)
      entries_length_m ↔
      ∀ v y n m : num_l ℳ, relation_l F (value_l a v) y → relation_l L a n →
        relation_l L v m → relation_l L y (add_l n m) := by
  simp only [entries_length_m, Formula.satisfies, output_syntax_l, SecondOrderPairing.edge_l]
  rfl

/-- 广义累计器折叠保持长度：折叠输出 `y` 的长度恰为源列表码与累计码长度之和。
对内部列表码 `a` 用真实公式 `entries_length_m` 作原列表归纳；折叠 cons 递推把累计值
更新为 `cons a v`，故归纳谓词对累计值 `v` 全称量化。长度非空分解经 `length_zero_l`／
`length_cons_l` 在实际长度图 `L` 与迭代图 `I` 上完成。 -/
theorem fold_length_l (hℳ : Theory.Models ℳ theory_m) {F L I : set_l ℳ}
    (hF : graph_semantics_l (graph_m (fold_m reverse_step_m)) F)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hI : graph_semantics_l (graph_m iterate_m) I) (a v y n m : num_l ℳ)
    (hy : relation_l F (value_l a v) y) (hla : relation_l L a n) (hlv : relation_l L v m) :
    relation_l L y (add_l n m) := by
  obtain ⟨C, _, hC⟩ := graph_total_l hℳ reverse_step_m
  let hfun := function_of_semantics_l hℳ length_m hL
  have h00 : relation_l L (zero_l ℳ) (zero_l ℳ) :=
    (SecondOrderProgramLength.length_rel_l hℳ hL hI (zero_l ℳ) (zero_l ℳ)).mpr
      ((length_zero_l hℳ hI (zero_l ℳ)).mpr rfl)
  have key : ∀ x : num_l ℳ, ∀ v y n m : num_l ℳ, relation_l F (value_l x v) y →
      relation_l L x n → relation_l L v m → relation_l L y (add_l n m) := by
    refine SecondOrderListInduction.list_induct_l hℳ entries_length_m
      entries_length_language_m (((Env.empty (M := ℳ)).pushFree L).pushFree F)
      (fun x => ∀ v y n m : num_l ℳ, relation_l F (value_l x v) y → relation_l L x n →
        relation_l L v m → relation_l L y (add_l n m))
      (fun x => entries_length_syntax_l F L x) ?_ ?_
    · -- 空码：折叠保持累计值（y = v），源长度 n = 0，故输出长度 = 0 + m = m。
      intro v y n m hy hla hlv
      have hyv : v = y := (reverse_fold_zero_l hℳ hF v y).mp hy
      have hn : n = zero_l ℳ := function_value_unique_l hfun hla h00
      subst hyv
      rw [hn, SecondOrderNumbers.zero_add_l hℳ m]
      exact hlv
    · -- cons 码：分解源长度与累计后继，再把归纳假设用于更新后的累计值 `cons a v`。
      intro a t ih v y n m hy hla hlv
      rw [reverse_fold_cons_l hℳ hF hC] at hy
      have hspec :=
        (SecondOrderProgramLength.length_rel_l hℳ hL hI (succ_l (value_l a t)) n).mp hla
      have hnz : succ_l (value_l a t) ≠ zero_l ℳ := nonzero_l hℳ (value_l a t)
      rcases predecessor_l hℳ n with rfl | ⟨k, rfl⟩
      · exact absurd ((length_zero_l hℳ hI (succ_l (value_l a t))).mp hspec) hnz
      · have hlt : relation_l L t k :=
          (SecondOrderProgramLength.length_rel_l hℳ hL hI t k).mpr
            ((length_cons_l hℳ hI a t k).mp hspec)
        have hlc : relation_l L (succ_l (value_l a v)) (succ_l m) :=
          (SecondOrderProgramLength.length_rel_l hℳ hL hI (succ_l (value_l a v)) (succ_l m)).mpr
            ((length_cons_l hℳ hI a v m).mpr
              ((SecondOrderProgramLength.length_rel_l hℳ hL hI v m).mp hlv))
        have hsum := ih (succ_l (value_l a v)) y k (succ_l m) hy hlt hlc
        rw [add_succ_l hℳ k m] at hsum
        rw [SecondOrderNumbers.succ_add_l hℳ k m]
        exact hsum
  exact key a v y n m hy hla hlv

/-- 原反转程序保持长度：`reverse_m` 输出 `y` 与输入 `a` 在长度图上取同一内部长度。
经阶段A 反转桥把 `reverse_m` 图归约到同一折叠的零初值调用，再用广义累计器长度保持与
`n + 0 = n` 收口。 -/
theorem reverse_length_l (hℳ : Theory.Models ℳ theory_m) {T F L I : set_l ℳ}
    (hT : graph_semantics_l (graph_m reverse_m) T)
    (hF : graph_semantics_l (graph_m (fold_m reverse_step_m)) F)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hI : graph_semantics_l (graph_m iterate_m) I) (a y n : num_l ℳ)
    (hay : relation_l T a y) (hla : relation_l L a n) :
    relation_l L y n := by
  have h00 : relation_l L (zero_l ℳ) (zero_l ℳ) :=
    (SecondOrderProgramLength.length_rel_l hℳ hL hI (zero_l ℳ) (zero_l ℳ)).mpr
      ((length_zero_l hℳ hI (zero_l ℳ)).mpr rfl)
  have hf := (reverse_bridge_l hℳ hT hF a y).mp hay
  have h := fold_length_l hℳ hF hL hI a (zero_l ℳ) y n (zero_l ℳ) hf hla h00
  rw [add_zero_l hℳ n] at h
  exact h

/-! ## 公理审计

本模块公共声明仅允许既有标准公理集合（propext/Quot.sound/Classical.choice），
无新增公理，亦不得有 `sorryAx`。审计置于命名空间内、`end` 之前。 -/

#print axioms entries_length_m
#print axioms entries_length_language_m
#print axioms entries_length_syntax_l
#print axioms fold_length_l
#print axioms reverse_length_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListReverseEntries
