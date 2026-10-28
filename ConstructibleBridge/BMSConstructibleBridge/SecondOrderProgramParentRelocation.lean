import BMSConstructibleBridge.SecondOrderProgramUniformParentSpecification
import BMSConstructibleBridge.SecondOrderProgramUniformParentOrder
import BMSConstructibleBridge.SecondOrderProgramEntry
import BMSConstructibleBridge.SecondOrderProgramLength

/-!
# 父搜索的最大候选搬运（阶段 A3 的最大性层）

`SecondOrderProgramUniformParentSpecification` 把 `parent_m` 的实际输出完全归约为
`eligible_l M J x r t i`（上一行的祖先成员、本行两个条目坐标的存在与严格比较）加
「目标之前没有更大的合格候选」。因此把一条父边从局部列搬到平坦列 `w·k + j`，
只需要三件事：候选合格性在 `w·k + i ↔ i` 下一致、内部数序的加法搬运、
以及父搜索规格本身。

本模块给出这条纯最大性搬运，不引用 `copy_m` / `copies_m`：前两条定理只用到本副本内的
候选，故不需要副本区间外的信息；缺项对应定理才需要「本副本之前的候选全部不合格」，
那正是父列落在好前缀或更早副本的情形。祖先半边与条目半边各自的一致性由 A3-a 与 A4
提供，在此作为显式前提 `hagree`。所有列号、行号、次数与宽度均可取内部非标准元素。

父搜索的目标界是所在行的内部长度，故局部侧显式要求 `j < w`、平坦侧要求 `w·k + j < m`：
两者都由各自行自身的长度关系给出，不由另一侧的界推出。数序一律取
`SecondOrderAlgebra.order_l` 实例的 `<`，与规格类型同形；内部正差见证只在算术引理内部用。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentRelocation

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramUniformParentSpecification
    (eligible_l parent_succ_some_l parent_succ_none_l)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramLength (length_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 内部数序被同侧加法保持：见证逐字搬运，不用类型类算术。 -/
theorem lt_add_left_l (hℳ : Theory.Models ℳ theory_m) {a b c : num_l ℳ} :
    letI := order_l hℳ
    a < b → add_l c a < add_l c b := by
  intro h
  letI := order_l hℳ
  obtain ⟨d, hd⟩ := h
  exact ⟨d, (SecondOrderNumbers.add_assoc_l hℳ c a (succ_l d)).trans (congrArg (add_l c) hd)⟩

/-- 同侧加法反射内部数序：消去加数后见证不变。 -/
theorem lt_of_add_lt_add_left_l (hℳ : Theory.Models ℳ theory_m) {a b c : num_l ℳ} :
    letI := order_l hℳ
    add_l c a < add_l c b → a < b := by
  intro h
  letI := order_l hℳ
  obtain ⟨d, hd⟩ := h
  exact ⟨d, (SecondOrderNumbers.add_cancel_l hℳ c _ _).mp
    ((SecondOrderNumbers.add_assoc_l hℳ c a (succ_l d)).symm.trans hd)⟩

/-- 偏移段内目标的任意实际父，要么已经落到偏移之前，要么仍是同一偏移下的局部列。
该粗分解只使用父列严格下降；它不把“偏移之前”误说成原好前缀。 -/
theorem parent_below_or_offset_l (hℳ : Theory.Models ℳ theory_m)
    {P : set_l ℳ} (hP : graph_semantics_l (graph_m parent_m) P)
    {x r K j c : num_l ℳ}
    (hp : relation_l P (value_l (value_l x r) (add_l K j)) (succ_l c)) :
    letI := semiring_l hℳ
    letI := order_l hℳ
    SecondOrderOrder.lt_l c K ∨ ∃ q, SecondOrderOrder.lt_l q j ∧ add_l K q = c := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  have hct : c < add_l K j :=
    SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hp
  by_cases hcK : c < K
  · exact Or.inl hcK
  · obtain ⟨q, hq⟩ := (le_iff_l hℳ K c).mp (le_of_not_gt hcK)
    rw [← hq] at hct
    exact Or.inr ⟨q, lt_of_add_lt_add_left_l hℳ hct, hq⟩

/-- 任意内部偏移 `K` 下，局部父边搬到偏移段中的对应父边。 -/
theorem parent_local_to_offset_l (hℳ : Theory.Models ℳ theory_m)
    {P L M J : set_l ℳ} (hP : graph_semantics_l (graph_m parent_m) P)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    {w K blk out m : num_l ℳ} (hw : relation_l L blk w) (hm : relation_l L out m)
    {r j i : num_l ℳ} :
    letI := semiring_l hℳ
    letI := order_l hℳ
    add_l K j < m →
      (∀ q, q < j →
        (eligible_l M J out r (add_l K j) (add_l K q) ↔
          eligible_l M J blk r j q)) →
      relation_l P (value_l (value_l blk (succ_l r)) j) (succ_l i) →
      relation_l P (value_l (value_l out (succ_l r)) (add_l K j))
        (succ_l (add_l K i)) := by
  intro hfm hagree hyp
  letI := semiring_l hℳ
  letI := order_l hℳ
  obtain ⟨hij, hel, hmax⟩ := ((parent_succ_some_l hℳ hP hL hM hJ hw r j i).mp hyp).2
  have hlt : add_l K i < add_l K j := lt_add_left_l hℳ hij
  have hel' : eligible_l M J out r (add_l K j) (add_l K i) :=
    (hagree i hij).mpr hel
  have hmax' : ∀ c, add_l K i < c → c < add_l K j →
      ¬ eligible_l M J out r (add_l K j) c := by
    intro c hc₁ hc₂ hc
    obtain ⟨d, hd⟩ := hc₁
    have heq : add_l K (add_l i (succ_l d)) = c :=
      ((SecondOrderNumbers.add_assoc_l hℳ K i (succ_l d)).symm.trans hd)
    have h2 : add_l K (add_l i (succ_l d)) < add_l K j := by rw [heq]; exact hc₂
    have hjE : add_l i (succ_l d) < j := lt_of_add_lt_add_left_l hℳ h2
    rw [← heq] at hc
    exact hmax (add_l i (succ_l d)) ⟨d, rfl⟩ hjE
      ((hagree (add_l i (succ_l d)) hjE).mp hc)
  exact (parent_succ_some_l hℳ hP hL hM hJ hm r (add_l K j) (add_l K i)).mpr
    ⟨hfm, hlt, hel', hmax'⟩

/-- 任意内部偏移 `K` 下，偏移段中的父边搬回局部父边。 -/
theorem parent_offset_to_local_l (hℳ : Theory.Models ℳ theory_m)
    {P L M J : set_l ℳ} (hP : graph_semantics_l (graph_m parent_m) P)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    {w K blk out m : num_l ℳ} (hw : relation_l L blk w) (hm : relation_l L out m)
    {r j i : num_l ℳ} :
    letI := semiring_l hℳ
    letI := order_l hℳ
    j < w →
      (∀ q, q < j →
        (eligible_l M J out r (add_l K j) (add_l K q) ↔
          eligible_l M J blk r j q)) →
      relation_l P (value_l (value_l out (succ_l r)) (add_l K j))
        (succ_l (add_l K i)) →
      relation_l P (value_l (value_l blk (succ_l r)) j) (succ_l i) := by
  intro hjw hagree hyp
  letI := semiring_l hℳ
  letI := order_l hℳ
  obtain ⟨hcij, hel, hmax⟩ :=
    ((parent_succ_some_l hℳ hP hL hM hJ hm r (add_l K j) (add_l K i)).mp hyp).2
  have hij : i < j := lt_of_add_lt_add_left_l hℳ hcij
  have hel' : eligible_l M J blk r j i := (hagree i hij).mp hel
  have hmax' : ∀ c, i < c → c < j → ¬ eligible_l M J blk r j c := by
    intro c hc₁ hc₂ hc
    exact absurd ((hagree c hc₂).mpr hc)
      (hmax (add_l K c) (lt_add_left_l hℳ hc₁) (lt_add_left_l hℳ hc₂))
  exact (parent_succ_some_l hℳ hP hL hM hJ hw r j i).mpr ⟨hjw, hij, hel', hmax'⟩

/-- 任意内部偏移 `K` 下，后继行的段内父边逐值对应。 -/
theorem parent_some_offset_congr_l (hℳ : Theory.Models ℳ theory_m)
    {P L M J : set_l ℳ} (hP : graph_semantics_l (graph_m parent_m) P)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    {w K blk out m : num_l ℳ} (hw : relation_l L blk w) (hm : relation_l L out m)
    {r j : num_l ℳ} :
    letI := semiring_l hℳ
    letI := order_l hℳ
    j < w → add_l K j < m →
      (∀ q, q < j →
        (eligible_l M J out r (add_l K j) (add_l K q) ↔
          eligible_l M J blk r j q)) →
      ∀ i, relation_l P (value_l (value_l out (succ_l r)) (add_l K j))
          (succ_l (add_l K i)) ↔
        relation_l P (value_l (value_l blk (succ_l r)) j) (succ_l i) := by
  intro hjw hKjm hagree i
  exact ⟨parent_offset_to_local_l hℳ hP hL hM hJ hw hm hjw hagree,
    parent_local_to_offset_l hℳ hP hL hM hJ hw hm hKjm hagree⟩

/-- 局部父边搬到平坦列：本行候选合格性在 `w·k + q ↔ q` 下一致时，副本内部的最大合格候选
搬运后仍是平坦目标的最大合格候选。 -/
theorem parent_local_to_flat_l (hℳ : Theory.Models ℳ theory_m)
    {P L M J : set_l ℳ} (hP : graph_semantics_l (graph_m parent_m) P)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    {w k blk out m : num_l ℳ} (hw : relation_l L blk w) (hm : relation_l L out m)
    {r j i : num_l ℳ} :
    letI := semiring_l hℳ
    letI := order_l hℳ
    add_l (mul_l w k) j < m →
      (∀ q, q < j →
        (eligible_l M J out r (add_l (mul_l w k) j) (add_l (mul_l w k) q) ↔
          eligible_l M J blk r j q)) →
      relation_l P (value_l (value_l blk (succ_l r)) j) (succ_l i) →
      relation_l P (value_l (value_l out (succ_l r)) (add_l (mul_l w k) j))
        (succ_l (add_l (mul_l w k) i)) := by
  intro hfm hagree hyp
  letI := semiring_l hℳ
  letI := order_l hℳ
  obtain ⟨hij, hel, hmax⟩ := ((parent_succ_some_l hℳ hP hL hM hJ hw r j i).mp hyp).2
  have hlt : add_l (mul_l w k) i < add_l (mul_l w k) j := lt_add_left_l hℳ hij
  have hel' : eligible_l M J out r (add_l (mul_l w k) j) (add_l (mul_l w k) i) :=
    (hagree i hij).mpr hel
  have hmax' : ∀ c, add_l (mul_l w k) i < c → c < add_l (mul_l w k) j →
      ¬ eligible_l M J out r (add_l (mul_l w k) j) c := by
    intro c hc₁ hc₂ hc
    obtain ⟨d, hd⟩ := hc₁
    have heq : add_l (mul_l w k) (add_l i (succ_l d)) = c :=
      ((SecondOrderNumbers.add_assoc_l hℳ (mul_l w k) i (succ_l d)).symm.trans hd)
    have h2 : add_l (mul_l w k) (add_l i (succ_l d)) < add_l (mul_l w k) j := by
      rw [heq]
      exact hc₂
    have hjE : add_l i (succ_l d) < j := lt_of_add_lt_add_left_l hℳ h2
    rw [← heq] at hc
    exact hmax (add_l i (succ_l d)) ⟨d, rfl⟩ hjE
      ((hagree (add_l i (succ_l d)) hjE).mp hc)
  exact (parent_succ_some_l hℳ hP hL hM hJ hm r (add_l (mul_l w k) j)
    (add_l (mul_l w k) i)).mpr ⟨hfm, hlt, hel', hmax'⟩

/-- 平坦父边搬回局部列：平坦目标的最大性限制到 `w·k + q` 形候选后，经 `hagree` 就是
局部目标的最大性；此处同样只用本副本内的候选。 -/
theorem parent_flat_to_local_l (hℳ : Theory.Models ℳ theory_m)
    {P L M J : set_l ℳ} (hP : graph_semantics_l (graph_m parent_m) P)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    {w k blk out m : num_l ℳ} (hw : relation_l L blk w) (hm : relation_l L out m)
    {r j i : num_l ℳ} :
    letI := semiring_l hℳ
    letI := order_l hℳ
    j < w →
      (∀ q, q < j →
        (eligible_l M J out r (add_l (mul_l w k) j) (add_l (mul_l w k) q) ↔
          eligible_l M J blk r j q)) →
      relation_l P (value_l (value_l out (succ_l r)) (add_l (mul_l w k) j))
        (succ_l (add_l (mul_l w k) i)) →
      relation_l P (value_l (value_l blk (succ_l r)) j) (succ_l i) := by
  intro hjw hagree hyp
  letI := semiring_l hℳ
  letI := order_l hℳ
  obtain ⟨hcij, hel, hmax⟩ :=
    ((parent_succ_some_l hℳ hP hL hM hJ hm r (add_l (mul_l w k) j)
      (add_l (mul_l w k) i)).mp hyp).2
  have hij : i < j := lt_of_add_lt_add_left_l hℳ hcij
  have hel' : eligible_l M J blk r j i := (hagree i hij).mp hel
  have hmax' : ∀ c, i < c → c < j → ¬ eligible_l M J blk r j c := by
    intro c hc₁ hc₂ hc
    exact absurd ((hagree c hc₂).mpr hc)
      (hmax (add_l (mul_l w k) c) (lt_add_left_l hℳ hc₁) (lt_add_left_l hℳ hc₂))
  exact (parent_succ_some_l hℳ hP hL hM hJ hw r j i).mpr ⟨hjw, hij, hel', hmax'⟩

/-- 两侧父输出同时缺失。两侧的界各来自所在行的长度，故两个界都显式给出；此时「越界」
分支两边同假，等价只剩候选合格性搬运。由平坦到局部一侧还需 `hbefore`：本副本之前的
候选（好前缀与更早副本）全部不合格，否则平坦目标可能落在区间外而局部侧看不到该候选。 -/
theorem parent_none_congr_l (hℳ : Theory.Models ℳ theory_m)
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
      (∀ q, q < mul_l w k → ¬ eligible_l M J out r (add_l (mul_l w k) j) q) →
      (relation_l P (value_l (value_l out (succ_l r)) (add_l (mul_l w k) j)) (zero_l ℳ) ↔
        relation_l P (value_l (value_l blk (succ_l r)) j) (zero_l ℳ)) := by
  intro hjw hfm hagree hbefore
  letI := semiring_l hℳ
  letI := order_l hℳ
  rw [parent_succ_none_l hℳ hP hL hM hJ hm r (add_l (mul_l w k) j),
    parent_succ_none_l hℳ hP hL hM hJ hw r j]
  constructor
  · rintro (hle | hall)
    · exact absurd hfm (not_lt_of_ge hle)
    · refine Or.inr (fun q (hqj : q < j) (hc : eligible_l M J blk r j q) =>
        hall (add_l (mul_l w k) q) (lt_add_left_l hℳ hqj) ((hagree q hqj).mpr hc))
  · rintro (hle | hall)
    · exact absurd hjw (not_lt_of_ge hle)
    · refine Or.inr (fun c (hc₁ : c < add_l (mul_l w k) j)
        (hc₂ : eligible_l M J out r (add_l (mul_l w k) j) c) => ?_)
      by_cases hck : c < mul_l w k
      · exact hbefore c hck hc₂
      · obtain ⟨e, he⟩ := (le_iff_l hℳ _ _).mp (le_of_not_gt hck)
        have he' : add_l (mul_l w k) e = c := he
        have h2 : add_l (mul_l w k) e < add_l (mul_l w k) j := by rw [he']; exact hc₁
        have hej : e < j := lt_of_add_lt_add_left_l hℳ h2
        rw [← he'] at hc₂
        exact absurd ((hagree e hej).mp hc₂) (hall e hej)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentRelocation
