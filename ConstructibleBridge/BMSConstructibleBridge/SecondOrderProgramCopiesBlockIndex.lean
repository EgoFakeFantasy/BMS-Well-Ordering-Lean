import BMSConstructibleBridge.SecondOrderProgramCopies
import BMSConstructibleBridge.SecondOrderProgramCopyBlock
import BMSConstructibleBridge.SecondOrderProgramCopyBlockShape
import BMSConstructibleBridge.SecondOrderProgramCopiesBlock
import BMSConstructibleBridge.SecondOrderProgramCopiesShape
import BMSConstructibleBridge.SecondOrderProgramListAppend
import BMSConstructibleBridge.SecondOrderProgramListShift

/-!
# 任意内部副本索引在原多副本输出中的列定位

`SecondOrderProgramCopiesBlock` 只闭合末尾块：复制次数 `succ s` 时读平坦列 `w·s + r`。
本模块把定位推广到任意内部副本下标。次数写成 `s + succ t`，对 `t` 作模型内部归纳：
`t = 0` 正是末尾块；归纳步里目标块落在新拼接的左段，先用真实宽度
`copies_width_l` / `copy_width_l` 与 `append_left_l` 剥掉右侧刚追加的一块，再用归纳假设。

归纳公式的自由槽为 `[q, s, blk, w, R, E]`，归纳变量是该上下文头部的自由变元，
故走 `SecondOrderModel.induct_l` 的自由变元形式；数量词只扩张绑定上下文，
所以自由槽在三个绑定下都不需弱化。算术只用零、后继、加、乘四个函数符号，
配对一律由原 `pair_m` 模板消去，成员关系走原 `output_m` 边模板。

`s`、`t`、块宽 `w`、局部列 `i`、原块与参数码都可取任意内部非标准元素；任意
`s < count` 恰由内部正差定义 `lt_l` 给出见证 `count = s + succ t`，因此不需要宿主
`Nat` 归纳，也不要求矩形性、生成性或外部标准性。本模块只定位列码本身：列内逐行
值变换属阶段 A2，父与祖先重定位属阶段 A3、A4。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopiesBlockIndex

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramCopies (copies_m copies_succ_l)
open SecondOrderProgramCopyBlock (copy_m)
open SecondOrderProgramCopiesBlock (block_read_last_l)
open SecondOrderProgramCopiesShape (copies_width_l)
open SecondOrderProgramCopyBlockShape (copy_width_l)
open SecondOrderProgramListAppend (append_m append_left_l)
open SecondOrderProgramListShift (output_m output_syntax_l)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 除归纳变量外的自由槽：`[参数码, 副本下标, 原块, 块宽, 多副本图, 查表图]`。 -/
private abbrev Δ5 : SortContext signature_m := [.num, .num, .num, .num, .set, .set]

/-- 归纳变量在头部的完整自由上下文 `[t, q, s, blk, w, R, E]`。 -/
private abbrev Φ : SortContext signature_m := .num :: Δ5

private def addT {Γ Δ : SortContext signature_m} (s t : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .add (.cons s (.cons t .nil))

private def mulT {Γ Δ : SortContext signature_m} (s t : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .mul (.cons s (.cons t .nil))

private def succT {Γ Δ : SortContext signature_m} (t : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .succ (.cons t .nil)

/-- 自由槽：`[t, q, s, blk, w, R, E]`，其中 `t` 为归纳变量；对任意绑定上下文多态，
因为数量词只扩张绑定上下文。 -/
private def slot_t {Γ : SortContext signature_m} : Term signature_m Γ Φ .num := .fvar .here

private def slot_q {Γ : SortContext signature_m} : Term signature_m Γ Φ .num :=
  .fvar (.there .here)

private def slot_s {Γ : SortContext signature_m} : Term signature_m Γ Φ .num :=
  .fvar (.there (.there .here))

private def slot_blk {Γ : SortContext signature_m} : Term signature_m Γ Φ .num :=
  .fvar (.there (.there (.there .here)))

private def slot_w {Γ : SortContext signature_m} : Term signature_m Γ Φ .num :=
  .fvar (.there (.there (.there (.there .here))))

private def slot_R {Γ : SortContext signature_m} : Term signature_m Γ Φ .set :=
  .fvar (.there (.there (.there (.there (.there .here)))))

private def slot_E {Γ : SortContext signature_m} : Term signature_m Γ Φ .set :=
  .fvar (.there (.there (.there (.there (.there (.there .here))))))

/-- 归纳正文：第 `s` 块之后还追加 `succ t` 份时，总输出的平坦列 `w·s + i` 与 `blk`
的第 `i` 列互推读值。三个绑定依次为总输出、局部列、读值。 -/
def relocation_m : Formula signature_m [] Φ :=
  .forallE .num
    (.imp (output_m slot_R slot_q (addT slot_s (succT slot_t)) (.bvar .here))
      (.forallE .num
        (.imp (PrimitiveFormulas.lt_m (.bvar .here) slot_w)
          (.forallE .num
            (.iff
              (output_m slot_E (.bvar (.there (.there .here)))
                (addT (mulT slot_w slot_s) (.bvar (.there .here))) (.bvar .here))
              (output_m slot_E slot_blk (.bvar (.there .here)) (.bvar .here)))))))

/-- 正文只用零、后继、加乘、成员与数量词，配对由原模板消去。 -/
theorem relocation_language_m : language_m relocation_m = true := pure_language_m _ rfl

/-- 把六个自由槽 `[q, s, blk, w, R, E]` 依次装入环境；归纳变量由 `pushFree` 追加在头部。 -/
private def envSlots {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (R E : set_l ℳ) (q s blk w : num_l ℳ) : Env ℳ [] Δ5 :=
  let η₀ := Env.pushFree (Env.empty (M := ℳ)) E
  let η₁ := Env.pushFree η₀ R
  let η₂ := Env.pushFree η₁ w
  let η₃ := Env.pushFree η₂ blk
  let η₄ := Env.pushFree η₃ s
  Env.pushFree η₄ q

/-- 实际公式的解释逐字等于所需的任意内部读值等价。 -/
theorem relocation_syntax_l (R E : set_l ℳ) (q s blk w t : num_l ℳ) :
    Formula.satisfies (Env.pushFree (envSlots R E q s blk w) t)
      relocation_m ↔
      ∀ v, relation_l R (value_l q (add_l s (succ_l t))) v → ∀ i,
        SecondOrderOrder.lt_l i w → ∀ a,
          relation_l E (value_l v (add_l (mul_l w s) i)) a ↔ relation_l E (value_l blk i) a := by
  simp only [relocation_m, slot_t, slot_q, slot_s, slot_blk, slot_w, slot_R, slot_E,
    envSlots, Formula.satisfies, output_syntax_l, SecondOrderOrder.formula_l,
    SecondOrderOrder.lt_l, addT, mulT, succT, Term.eval, Arguments.eval,
    Env.pushBound, Env.pushFree, Assignment.push]
  rfl

/-- 任意内部 `s` 与追加偏移 `t`：`s + succ t` 份复制的总输出在第 `s` 块第 `i` 列的读值，
与直接读同一 `copy_m` 输出 `blk` 的第 `i` 列一致。 -/
theorem block_read_shift_l (hℳ : Theory.Models ℳ theory_m) {R C L E : set_l ℳ}
    (hR : graph_semantics_l (graph_m copies_m) R)
    (hC : graph_semantics_l (graph_m copy_m) C)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    {b A l w : num_l ℳ} (hb : relation_l L b w)
    {s blk : num_l ℳ} (hblk : relation_l C (value_l b (value_l A (value_l s l))) blk)
    {t i : num_l ℳ} (hi : SecondOrderOrder.lt_l i w)
    {y : num_l ℳ}
    (hy : relation_l R (value_l (value_l b (value_l A l)) (add_l s (succ_l t))) y)
    (a : num_l ℳ) :
    relation_l E (value_l y (add_l (mul_l w s) i)) a ↔ relation_l E (value_l blk i) a := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  obtain ⟨Ap, _, hAp⟩ := graph_total_l hℳ append_m
  refine (induct_l hℳ relocation_m relocation_language_m
    (envSlots R E (value_l b (value_l A l)) s blk w)
    (fun n => ∀ v, relation_l R (value_l (value_l b (value_l A l)) (add_l s (succ_l n))) v →
      ∀ j, SecondOrderOrder.lt_l j w → ∀ c,
        relation_l E (value_l v (add_l (mul_l w s) j)) c ↔ relation_l E (value_l blk j) c)
    (fun n => relocation_syntax_l R E (value_l b (value_l A l)) s blk w n) ?_ ?_ t)
    y hy i hi a
  · -- 基例：`s + succ 0 = succ s`，正是已验的末尾块定位。
    intro v hv j hj c
    have hzero : add_l s (succ_l (zero_l ℳ)) = succ_l s := by
      rw [add_succ_l hℳ, add_zero_l hℳ]
    rw [hzero] at hv
    exact block_read_last_l hℳ hR hC hL hE hb hblk hv hj c
  · -- 归纳步：先剥掉右侧刚追加的一块，目标块留在左段，再用归纳假设。
    intro n ih v hv j hj c
    have hsucc : add_l s (succ_l (succ_l n)) = succ_l (add_l s (succ_l n)) :=
      add_succ_l hℳ s (succ_l n)
    rw [hsucc] at hv
    obtain ⟨u, blk', hu, hblk', happend⟩ :=
      (copies_succ_l hℳ hR hC hAp b A l (add_l s (succ_l n)) v).mp hv
    have hlt : add_l (mul_l w s) j < mul_l w (succ_l s) := by
      obtain ⟨k, hk⟩ := hj
      refine ⟨k, ?_⟩
      calc add_l (add_l (mul_l w s) j) (succ_l k)
          = add_l (mul_l w s) (add_l j (succ_l k)) :=
            SecondOrderNumbers.add_assoc_l hℳ _ _ _
        _ = add_l (mul_l w s) w := congrArg (add_l (mul_l w s)) hk
        _ = mul_l w (succ_l s) := (mul_succ_l hℳ w s).symm
    have hle : succ_l s ≤ add_l s (succ_l n) := (le_iff_l hℳ _ _).mpr ⟨n,
      (SecondOrderNumbers.succ_add_l hℳ s n).trans (add_succ_l hℳ s n).symm⟩
    exact ((append_left_l hℳ hAp hL hE (copies_width_l hℳ hR hL hb hu)
      (copy_width_l hℳ hC hL hblk' hb) happend
      (lt_of_lt_of_le hlt (mul_le_mul_of_nonneg_left hle (zero_le_l hℳ w))) c).trans
      (ih u hu j hj c))

/-- 消费者形式：任意内部 `s < count` 的块定位，次数无需写成显式加法。 -/
theorem block_read_index_l (hℳ : Theory.Models ℳ theory_m) {R C L E : set_l ℳ}
    (hR : graph_semantics_l (graph_m copies_m) R)
    (hC : graph_semantics_l (graph_m copy_m) C)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    {b A l w : num_l ℳ} (hb : relation_l L b w)
    {s blk count y i : num_l ℳ} (hs : SecondOrderOrder.lt_l s count)
    (hblk : relation_l C (value_l b (value_l A (value_l s l))) blk)
    (hy : relation_l R (value_l (value_l b (value_l A l)) count) y)
    (hi : SecondOrderOrder.lt_l i w) (a : num_l ℳ) :
    relation_l E (value_l y (add_l (mul_l w s) i)) a ↔ relation_l E (value_l blk i) a := by
  obtain ⟨t, ht⟩ := hs
  rw [← ht] at hy
  exact block_read_shift_l hℳ hR hC hL hE hb hblk hi hy a

#print axioms relocation_m
#print axioms relocation_language_m
#print axioms relocation_syntax_l
#print axioms block_read_shift_l
#print axioms block_read_index_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopiesBlockIndex
