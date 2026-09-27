import BMSConstructibleBridge.SecondOrderProgramUniformParentPrefix
import BMSConstructibleBridge.SecondOrderProgramListShift
import BMSConstructibleBridge.SecondOrderProgramLength
import BMSConstructibleBridge.SecondOrderProgramUniformParent
import BMSConstructibleBridge.SecondOrderProgramUniformParentSpecification
import BMSConstructibleBridge.SecondOrderProgramAncestorMembership
import BMSConstructibleBridge.SecondOrderProgramEntry
import BMSConstructibleBridge.SecondOrderProgramParentRelocation
import BMSConstructibleBridge.PrimitiveFormulas

/-!
# 副本列平移的前缀父不变式（阶段 A3 实质关口的行归纳公式）

`SecondOrderProgramParentRelocation` 的三条搬运引理把父边搬迁完全归约到前提
`hagree q : eligible M J out r (K+j) (K+q) ↔ eligible M J blk r j q`（`K = mul w k`）。
`hagree` 的坐标比较半边由 `SecondOrderProgramCopiesBlockEntry.block_compare_agree_l`
直接给出；祖先成员半边由 `ancestor_shift_l` 给出，而它唯一的非平凡前提正是本模块要表达的
**父列平移对应** `hpp`。

已从实际源码确认父平移的真正依据**不是列内容的取值平移**：`eligible_l` 的坐标比较走
entry 图 `entry_m`（J），而 `block_entry_agree_l` / `block_compare_agree_l` 证明 J 逐内部行、
逐候选列在副本平坦列与原块同局部列之间**与 copy 下标无关**地一致；列内容 `lookup_m`（E）的
`+k·(last-first)` 值平移属另一关系，不进入 eligible，不可用作父平移的理由（曾据此误判，已撤回）。
因此 `out` 在列 `K+j` 的父等于 `blk` 在列 `j` 的父**平移 `K`**，其残留条件全在 eligible 的
另一半边——**祖先成员** `¬M`：`K+j` 的祖先链若全程留在本副本内则平移对应成立，链一旦跳到更早副本
或好前缀，父列即落在别处——这正是手册要求的六情形来源，也是 `hpp` 与 `hbefore` 同源、须由同一条
按行归纳不变式一次给出的原因。

本模块只做**编码层**：定义按行归纳的平移前缀公式 `shift_prefix_m`、证明它属于原纯语言、
并给出它在真实结构上的逐字解释桥。零行 / 后继行两支与 `hpp` 出口在后续模块消费此桥。
所有列号、行号、块宽与偏移 `K` 都可取任意内部非标准元素；归纳变量是行号 `r`，走
`SecondOrderModel.induct_l` 的自由变元形式，不使用宿主 `Nat` 归纳。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopiesBlockParentShift

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramListShift (output_m output_syntax_l)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramUniformParentPrefix (at_row_m at_row_syntax_l)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramUniformParentSpecification (eligible_l parent_succ_some_l)
open SecondOrderProgramParentRelocation
  (lt_add_left_l parent_local_to_flat_l parent_flat_to_local_l parent_none_congr_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 除归纳行 `r` 外的自由槽 `[父图, 平坦数组, 局部块, 块起点偏移, 块宽]`。 -/
private abbrev Δ : SortContext signature_m := [.set, .num, .num, .num, .num]

/-- 归纳变量在头部的完整自由上下文 `[r, 父图, out, blk, K, w]`。 -/
private abbrev Φ : SortContext signature_m := .num :: Δ

private def zeroT {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .zero .nil

private def succT {Γ Δ : SortContext signature_m} (t : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .succ (.cons t .nil)

private def addT {Γ Δ : SortContext signature_m} (s t : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .add (.cons s (.cons t .nil))

private def slot_r {Γ : SortContext signature_m} : Term signature_m Γ Φ .num := .fvar .here

private def slot_P {Γ : SortContext signature_m} : Term signature_m Γ Φ .set :=
  .fvar (.there .here)

private def slot_out {Γ : SortContext signature_m} : Term signature_m Γ Φ .num :=
  .fvar (.there (.there .here))

private def slot_blk {Γ : SortContext signature_m} : Term signature_m Γ Φ .num :=
  .fvar (.there (.there (.there .here)))

private def slot_K {Γ : SortContext signature_m} : Term signature_m Γ Φ .num :=
  .fvar (.there (.there (.there (.there .here))))

private def slot_w {Γ : SortContext signature_m} : Term signature_m Γ Φ .num :=
  .fvar (.there (.there (.there (.there (.there .here)))))

/-- 归纳正文：行 `r` 上，对全部块内列 `k < w` 与全部输出 `z`，平坦数组在列 `K+k` 的父输出
等于局部块在列 `k` 的父输出平移 `K`（`none` 对应 `none`，`succ p` 对应 `succ (K+p)`）。
三个绑定依次为列 `k`、输出 `z`、内部父列见证 `p`。 -/
def shift_prefix_m : Formula signature_m [] Φ :=
  .forallE .num
    (.imp (PrimitiveFormulas.lt_m (.bvar .here) slot_w)
      (.forallE .num
        (.iff
          (at_row_m slot_P slot_out slot_r (addT slot_K (.bvar (.there .here))) (.bvar .here))
          (.disj
            (.conj (.equal (.bvar .here) zeroT)
              (at_row_m slot_P slot_blk slot_r (.bvar (.there .here)) zeroT))
            (.existsE .num
              (.conj
                (.equal (.bvar (.there .here)) (succT (addT slot_K (.bvar .here))))
                (at_row_m slot_P slot_blk slot_r (.bvar (.there (.there .here)))
                  (succT (.bvar .here)))))))))

/-- 平移前缀公式只用零、后继、加、成员与数量词，配对由原 `pair_m` 模板消去。 -/
theorem shift_prefix_language_m : language_m shift_prefix_m = true := pure_language_m _ rfl

/-- 把五个自由槽 `[父图, out, blk, K, w]` 依次装入环境；归纳行由 `pushFree` 追加在头部。 -/
private def envSlots {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (P : set_l ℳ) (out blk K w : num_l ℳ) : Env ℳ [] Δ :=
  let η₀ := Env.pushFree (Env.empty (M := ℳ)) w
  let η₁ := Env.pushFree η₀ K
  let η₂ := Env.pushFree η₁ blk
  let η₃ := Env.pushFree η₂ out
  Env.pushFree η₃ P

/-- 实际公式的解释逐字等于所需的任意内部行父列平移对应。 -/
theorem shift_prefix_syntax_l (P : set_l ℳ) (out blk K w r : num_l ℳ) :
    Formula.satisfies (Env.pushFree (envSlots P out blk K w) r) shift_prefix_m ↔
      ∀ k, SecondOrderOrder.lt_l k w → ∀ z,
        relation_l P (value_l (value_l out r) (add_l K k)) z ↔
          (z = zero_l ℳ ∧ relation_l P (value_l (value_l blk r) k) (zero_l ℳ)) ∨
            ∃ p, z = succ_l (add_l K p) ∧
              relation_l P (value_l (value_l blk r) k) (succ_l p) := by
  simp only [shift_prefix_m, slot_r, slot_P, slot_out, slot_blk, slot_K, slot_w, envSlots,
    Formula.satisfies, SecondOrderOrder.formula_l, at_row_syntax_l, zeroT, succT, addT,
    Term.eval, Arguments.eval, Env.pushBound, Env.pushFree, Assignment.push]
  rfl

#print axioms shift_prefix_m
#print axioms shift_prefix_language_m
#print axioms shift_prefix_syntax_l

/-!
## 正确的行归纳载体：`≥ K` 段父输出逐字跟踪局部块父输出

`shift_prefix_m` 是「平坦父 = 局部父平移 `K` 且 `none↔none`」的**强**形式，在块底列
（局部父为 `none` 而平坦父可落到更早副本 `< K`）处为假，不能直接作归纳不变式。
真正成立且足以驱动链段对应的弱化形式是：**平坦父只要落在本副本段 `[K, K+w)`，就逐字等于
局部父平移 `K`**，即 `parent(out, r, K+k) = succ(K+p) ↔ parent(blk, r, k) = succ p`。
父列严格下降，故平坦链一旦落到 `< K` 就不再回到 `[K, K+w)`；于是对 `q < w`，
`K+q` 是 `K+j` 的祖先 ⟺ `q` 是 `j` 的祖先——这正是 hagree 唯一缺的祖先成员半边。
-/

/-- 弱化行不变式：块内列 `k < w` 上，平坦父若形如 `succ (K + p)` 当且仅当局部父为 `succ p`。
两个绑定依次为列 `k` 与内部父列见证 `p`；不含 `none↔none` 假支。 -/
def reloc_ge_m : Formula signature_m [] Φ :=
  .forallE .num
    (.imp (PrimitiveFormulas.lt_m (.bvar .here) slot_w)
      (.forallE .num
        (.iff
          (at_row_m slot_P slot_out slot_r (addT slot_K (.bvar (.there .here)))
            (succT (addT slot_K (.bvar .here))))
          (at_row_m slot_P slot_blk slot_r (.bvar (.there .here))
            (succT (.bvar .here))))))

/-- 弱化不变式仍只用零、后继、加、成员与数量词。 -/
theorem reloc_ge_language_m : language_m reloc_ge_m = true := pure_language_m _ rfl

/-- 弱化不变式在真实结构上的逐字解释：块内列的 `≥ K` 段父输出与局部块父输出同步。 -/
theorem reloc_ge_syntax_l (P : set_l ℳ) (out blk K w r : num_l ℳ) :
    Formula.satisfies (Env.pushFree (envSlots P out blk K w) r) reloc_ge_m ↔
      ∀ k, SecondOrderOrder.lt_l k w → ∀ p,
        relation_l P (value_l (value_l out r) (add_l K k)) (succ_l (add_l K p)) ↔
          relation_l P (value_l (value_l blk r) k) (succ_l p) := by
  simp only [reloc_ge_m, slot_r, slot_P, slot_out, slot_blk, slot_K, slot_w, envSlots,
    Formula.satisfies, SecondOrderOrder.formula_l, at_row_syntax_l, succT, addT,
    Term.eval, Arguments.eval, Env.pushBound, Env.pushFree, Assignment.push]
  rfl

#print axioms reloc_ge_m
#print axioms reloc_ge_language_m
#print axioms reloc_ge_syntax_l

/-- 平坦目标 `K+j` 的父若为 `succ c`，而本副本段存在合格候选 `K+q`（`q < j`），则该父列
不可能落在跨块段 `[0, K)`：`K+q` 的指标已压过任何 `< K` 的候选，与最大性支矛盾。
这是修正后的联合下降所依赖的「指标支配」核心引理，只用 `parent_succ_some_l` 的最大性与内部数序。 -/
theorem flat_parent_within_dominates_l (hℳ : Theory.Models ℳ theory_m)
    {P L M J : set_l ℳ} (hP : graph_semantics_l (graph_m parent_m) P)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    {out n K c q : num_l ℳ} (ho : relation_l L out n) (r j : num_l ℳ) :
    letI := semiring_l hℳ
    letI := order_l hℳ
    q < j →
      eligible_l M J out r (add_l K j) (add_l K q) →
      relation_l P (value_l (value_l out (succ_l r)) (add_l K j)) (succ_l c) →
      ¬ c < K := by
  intro hqj hel hyp
  letI := semiring_l hℳ
  letI := order_l hℳ
  obtain ⟨_, _, _, hmax⟩ := (parent_succ_some_l hℳ hP hL hM hJ ho r (add_l K j) c).mp hyp
  intro hck
  have hKq : K ≤ add_l K q := (le_iff_l hℳ _ _).mpr ⟨q, rfl⟩
  exact absurd hel (hmax (add_l K q) (lt_of_lt_of_le hck hKq) (lt_add_left_l hℳ hqj))

#print axioms flat_parent_within_dominates_l

/-- 弱化平移 `hge`（块内列 `K+k` 的 `≥K` 段父输出逐字跟踪局部父）把该列的任一平坦父输出
`succ c` 分解为两支：要么 `c = K + p` 且局部父正是 `succ p`（链仍在本副本段内），要么
`c < K`（链已跳到更早副本 / 好前缀，出界后由于父列严格降列不再回到 `[K,K+w)`）。这是
`ancestor_chain_from_reloc_ge` 步例的核心分情形，只用 `reloc_ge` 与内部线序，不假设父列只平移。 -/
theorem reloc_ge_target_cases_l (hℳ : Theory.Models ℳ theory_m) {P : set_l ℳ}
    {out blk K k c r : num_l ℳ}
    (hge : ∀ p, relation_l P (value_l (value_l out r) (add_l K k)) (succ_l (add_l K p)) ↔
                 relation_l P (value_l (value_l blk r) k) (succ_l p))
    (hc : relation_l P (value_l (value_l out r) (add_l K k)) (succ_l c)) :
    letI := order_l hℳ
    (∃ p, c = add_l K p ∧ relation_l P (value_l (value_l blk r) k) (succ_l p)) ∨
      SecondOrderOrder.lt_l c K := by
  classical
  letI := semiring_l hℳ
  letI := order_l hℳ
  by_cases hlt : c < K
  · exact Or.inr hlt
  · obtain ⟨p, hp⟩ := (le_iff_l hℳ K c).mp (le_of_not_gt hlt)
    rw [← hp] at hc
    exact Or.inl ⟨p, hp.symm, (hge p).mp hc⟩

#print axioms reloc_ge_target_cases_l

/-- 父列平移对应 `hpp` 的 some 支在块内列上逐值等价：给定本行候选合格性 `hagree`
（在 `K+q ↔ q` 下一致）、局部块宽界 `j < w` 与平坦界 `K + j < m`，某后继行局部父边
`P (blk, succ r, j) = succ i` 当且仅当平坦父边 `P (out, succ r, K + j) = succ (K + i)`。
两支直接由 `parent_local_to_flat_l` / `parent_flat_to_local_l` 组装，不消费 `hbefore`——
`hbefore` 只在 none 支（`parent_none_congr_l`）出现，于是本引理把开放问题精确收窄到 none 支。
列号、行号、块宽与偏移 `K = mul w k` 均取模型内部非标准元素，不做宿主 `Nat` 归纳。 -/
theorem parent_some_congr_l (hℳ : Theory.Models ℳ theory_m)
    {P L M J : set_l ℳ} (hP : graph_semantics_l (graph_m parent_m) P)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    {w k blk out m : num_l ℳ} (hw : relation_l L blk w) (hm : relation_l L out m)
    {r j : num_l ℳ} :
    letI := semiring_l hℳ
    letI := order_l hℳ
    j < w →
      add_l (mul_l w k) j < m →
      (∀ q, q < j →
        (eligible_l M J out r (add_l (mul_l w k) j) (add_l (mul_l w k) q) ↔
          eligible_l M J blk r j q)) →
      ∀ i, relation_l P (value_l (value_l blk (succ_l r)) j) (succ_l i) ↔
        relation_l P (value_l (value_l out (succ_l r)) (add_l (mul_l w k) j))
          (succ_l (add_l (mul_l w k) i)) := by
  intro hjw hfm hagree i
  constructor
  · exact fun h => parent_local_to_flat_l hℳ hP hL hM hJ hw hm hfm hagree h
  · exact fun h => parent_flat_to_local_l hℳ hP hL hM hJ hw hm hjw hagree h

#print axioms parent_some_congr_l

/-- 由本行候选合格性 `hagree` 与更早候选不合格 `hbefore` 一次给出父列平移对应 `hpp` 于
后继行标签 `succ r`：块内列 `K + j`（`K = mul w kc`、`j < w`、`K + j < m`）的实际父图输出
`z` 恰为「`z = 0` 且局部父 none」或「`z = succ (K + q)` 且局部父 `succ q`」。
`z` 按 `predecessor_l` 分零／后继两支：零支用 `parent_none_congr_l`；后继支先用 `hbefore`
（借 `parent_succ_some_l` 的合格性合取支）排除 `p < K`，再 `le_iff_l` 取 `p = K + q`，
两向分别用 `parent_flat_to_local_l` / `parent_local_to_flat_l`。
这是按行归纳步的父半边，some 支不消费 `hbefore`、none 支消费，`hbefore` 由上游好块假设给出。
列号、行号、块宽、copy 索引与偏移全部取模型内部非标准元素，无宿主 `Nat` 归纳。 -/
theorem hpp_succ_l (hℳ : Theory.Models ℳ theory_m)
    {P L M J : set_l ℳ} (hP : graph_semantics_l (graph_m parent_m) P)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    {w kc blk out m : num_l ℳ} (hw : relation_l L blk w) (hm : relation_l L out m)
    {r : num_l ℳ} :
    letI := semiring_l hℳ
    letI := order_l hℳ
    ∀ j, j < w →
      add_l (mul_l w kc) j < m →
      (∀ q, q < j →
        (eligible_l M J out r (add_l (mul_l w kc) j) (add_l (mul_l w kc) q) ↔
          eligible_l M J blk r j q)) →
      (∀ q, q < mul_l w kc → ¬ eligible_l M J out r (add_l (mul_l w kc) j) q) →
      ∀ z, relation_l P (value_l (value_l out (succ_l r)) (add_l (mul_l w kc) j)) z ↔
        ((z = zero_l ℳ ∧
            relation_l P (value_l (value_l blk (succ_l r)) j) (zero_l ℳ)) ∨
          ∃ q, z = succ_l (add_l (mul_l w kc) q) ∧
            relation_l P (value_l (value_l blk (succ_l r)) j) (succ_l q)) := by
  intro j hjw hfm hagree hbefore z
  letI := semiring_l hℳ
  letI := order_l hℳ
  constructor
  · intro hz
    rcases predecessor_l hℳ z with rfl | ⟨p, rfl⟩
    · rw [parent_none_congr_l hℳ hP hL hM hJ hw hm hjw hfm hagree hbefore] at hz
      exact Or.inl ⟨rfl, hz⟩
    · have hnelig : ¬ p < mul_l w kc := by
        intro hlt
        obtain ⟨_, _, hsel, _⟩ :=
          (parent_succ_some_l hℳ hP hL hM hJ hm r (add_l (mul_l w kc) j) p).mp hz
        exact absurd hsel (hbefore p hlt)
      obtain ⟨q, hKq⟩ := (le_iff_l hℳ (mul_l w kc) p).mp (le_of_not_gt hnelig)
      rw [← hKq] at hz
      exact Or.inr ⟨q, congrArg succ_l hKq.symm,
        parent_flat_to_local_l hℳ hP hL hM hJ hw hm hjw hagree hz⟩
  · rintro (⟨rfl, hz⟩ | ⟨q, rfl, hq⟩)
    · rw [parent_none_congr_l hℳ hP hL hM hJ hw hm hjw hfm hagree hbefore]
      exact hz
    · exact parent_local_to_flat_l hℳ hP hL hM hJ hw hm hfm hagree hq

#print axioms hpp_succ_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopiesBlockParentShift
