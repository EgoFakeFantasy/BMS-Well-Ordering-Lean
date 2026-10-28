import BMSConstructibleBridge.SecondOrderProgramCopyBlock
import BMSConstructibleBridge.SecondOrderProgramCopyBlockLookup
import BMSConstructibleBridge.SecondOrderProgramCopyEntry
import BMSConstructibleBridge.SecondOrderProgramCopyOptional
import BMSConstructibleBridge.SecondOrderProgramCopies
import BMSConstructibleBridge.SecondOrderProgramCopiesBlock
import BMSConstructibleBridge.SecondOrderProgramListCode
import BMSConstructibleBridge.SecondOrderProgramListLookup
import BMSConstructibleBridge.SecondOrderProgramAscending
import BMSConstructibleBridge.SecondOrderProgramOptionalLookup
import BMSConstructibleBridge.SecondOrderProgramSubtraction

/-!
# 复制块的逐内部行值公式（阶段 A2 局部层）

先把原共享参数图 `parameter_m` 在内部分解为
`pair 上升参数 (pair 复制次数 (pair 首列 末列))`，其中首列由同一 `head_m` 图给出；
再把已验的块读取 `copy_column_l`、列读取 `column_entry_l`、条目分支 `entry_rel_l`
与数值分支 `update_none_l` / `update_some_l` 串成一条完整值公式。

四类分支全部保留：上升测试输出零时值不变；首列或末列在该行缺项（Option 码为零）时值不变；
两项都存在时值精确是原值加同一截断差值的复制次数倍；合法 `some 0` 的码是 `succ zero`，
与原 `none` 的零码在同一可选图上互斥，绝不混同。

次数 `k`、块宽 `w`、列 `j`、行 `r`、各列码与长度都可取任意内部非标准元素；
界只由 `SecondOrderOrder.lt_l` 的内部正差见证给出，不使用宿主 `Nat` 归纳，
不要求矩形性、生成性或外部标准性。先对单个 `copy_m` 输出证明局部公式，
再经 A1 的列定位 `block_read_last_l` 平移到 `copies_m` 末尾副本的平坦列。
父/祖先重定位属阶段 A3、A4，不在本模块。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyShiftEntry

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality SecondOrderProgramValue
open SecondOrderProgramCallbackValue
open SecondOrderProgramCopyBlock (copy_m column_m parameter_m)
open SecondOrderProgramCopyBlockLookup (copy_column_l column_entry_l)
open SecondOrderProgramCopyEntry (entry_m entry_rel_l)
open SecondOrderProgramCopies (copies_m)
open SecondOrderProgramCopiesBlock (block_read_last_l)
open SecondOrderProgramListCode (head_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramAscending (ascending_m)
open SecondOrderProgramOptionalLookup (optional_m)
open SecondOrderProgramSubtraction (sub_m)
open SecondOrderProgramLength (length_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原共享参数图在任意内部输入上的精确分解：块 `pair 上升参数 (pair 次数 末列)`
映到 `pair 上升参数 (pair 次数 (pair 首列 末列))`，首列取自同一 `head_m` 图。 -/
theorem parameter_decode_l (hℳ : Theory.Models ℳ theory_m) {P H : set_l ℳ}
    (hP : graph_semantics_l (graph_m parameter_m) P)
    (hH : graph_semantics_l (graph_m head_m) H)
    (b A k l f : num_l ℳ) (hf : relation_l H b f) :
    relation_l P (value_l b (value_l A (value_l k l)))
      (value_l A (value_l k (value_l f l))) := by
  obtain ⟨g, hg, hga⟩ := value_exists_l hℳ head_m hH
  have hc1 : value_spec_l (.comp .left .right) _ :=
    comp_value_l hℳ (left_value_l hℳ) (right_value_l hℳ)
  have hc2 : value_spec_l (.comp (.comp .left .right) .right) _ :=
    comp_value_l hℳ hc1 (right_value_l hℳ)
  have hc3 : value_spec_l (.comp head_m .left) _ :=
    comp_value_l hℳ hg (left_value_l hℳ)
  have hc4 : value_spec_l (.comp (.comp .right .right) .right) _ :=
    comp_value_l hℳ (comp_value_l hℳ (right_value_l hℳ) (right_value_l hℳ)) (right_value_l hℳ)
  have hs : value_spec_l parameter_m _ :=
    pair_value_l hℳ hc1 (pair_value_l hℳ hc2 (pair_value_l hℳ hc3 hc4))
  have hgf : g b = f :=
    function_value_unique_l (function_of_semantics_l hℳ head_m hH) (hga b) hf
  exact (hs hP _ _).mpr (by simp only [hgf, SecondOrderUnpairing.unpair_l])

/-- 单个复制块输出在第 `j` 列、第 `r` 行的读值完整分支公式：源块列码 `s` 的该行为 `v`，
值不变当且仅当上升测试输出零，否则由首末列在该行的原 Option 码决定。 -/
theorem copy_entry_value_l (hℳ : Theory.Models ℳ theory_m)
    {C H L E B O U : set_l ℳ}
    (hC : graph_semantics_l (graph_m copy_m) C)
    (hH : graph_semantics_l (graph_m head_m) H)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hB : graph_semantics_l (graph_m ascending_m) B)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hU : graph_semantics_l (graph_m SecondOrderProgramCopyOptional.update_m) U)
    {b A k l blk f : num_l ℳ} (hf : relation_l H b f)
    (hblk : relation_l C (value_l b (value_l A (value_l k l))) blk)
    {w j s n r v : num_l ℳ} (hw : relation_l L b w) (hj : SecondOrderOrder.lt_l j w)
    (hs : relation_l E (value_l b j) s) (hn : relation_l L s n)
    (hr : SecondOrderOrder.lt_l r n) (hv : relation_l E (value_l s r) v)
    (colj y : num_l ℳ) (hcol : relation_l E (value_l blk j) colj) :
    relation_l E (value_l colj r) y ↔
      (relation_l B (value_l A (value_l j r)) (zero_l ℳ) ∧ v = y) ∨
        (¬relation_l B (value_l A (value_l j r)) (zero_l ℳ) ∧ ∃ first last,
          relation_l O (value_l f r) first ∧ relation_l O (value_l l r) last ∧
            relation_l U (value_l v (value_l k (value_l first last))) y) := by
  obtain ⟨K, _, hK⟩ := graph_total_l hℳ column_m
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ parameter_m
  obtain ⟨Ae, _, hAe⟩ := graph_total_l hℳ entry_m
  have hcq : relation_l K
      (value_l (value_l A (value_l k (value_l f l))) (value_l j s)) colj :=
    (copy_column_l hℳ hC hK hP hL hE hblk
      (parameter_decode_l hℳ hP hH b A k l f hf) hw hj hs).mp hcol
  exact (column_entry_l hℳ hK hAe hL hE hcq hn hr hv).trans
    (entry_rel_l hℳ hAe hB hO hU A k f l j r v y)

/-- 上升测试输出零，或首末列任一在该行缺项时，复制块该位置保持原值。 -/
theorem copy_entry_asis_l (hℳ : Theory.Models ℳ theory_m)
    {C H L E B O U : set_l ℳ}
    (hC : graph_semantics_l (graph_m copy_m) C)
    (hH : graph_semantics_l (graph_m head_m) H)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hB : graph_semantics_l (graph_m ascending_m) B)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hU : graph_semantics_l (graph_m SecondOrderProgramCopyOptional.update_m) U)
    {b A k l blk f : num_l ℳ} (hf : relation_l H b f)
    (hblk : relation_l C (value_l b (value_l A (value_l k l))) blk)
    {w j s n r v colj : num_l ℳ} (hw : relation_l L b w) (hj : SecondOrderOrder.lt_l j w)
    (hs : relation_l E (value_l b j) s) (hn : relation_l L s n)
    (hr : SecondOrderOrder.lt_l r n) (hv : relation_l E (value_l s r) v)
    (hcol : relation_l E (value_l blk j) colj)
    (hkeep : relation_l B (value_l A (value_l j r)) (zero_l ℳ) ∨
        ∃ first last, relation_l O (value_l f r) first ∧ relation_l O (value_l l r) last ∧
          (first = zero_l ℳ ∨ last = zero_l ℳ)) :
    relation_l E (value_l colj r) v := by
  classical
  rw [copy_entry_value_l hℳ hC hH hL hE hB hO hU hf hblk hw hj hs hn hr hv colj v hcol]
  by_cases hBz : relation_l B (value_l A (value_l j r)) (zero_l ℳ)
  · exact Or.inl ⟨hBz, rfl⟩
  · rcases hkeep with h | ⟨first, last, hfo, hla, h0⟩
    · exact absurd h hBz
    · refine Or.inr ⟨hBz, first, last, hfo, hla, ?_⟩
      rcases h0 with rfl | rfl
      · exact (SecondOrderProgramCopyOptional.update_none_l hℳ hU v k (zero_l ℳ) last v (Or.inl rfl)).mpr rfl
      · exact (SecondOrderProgramCopyOptional.update_none_l hℳ hU v k first (zero_l ℳ) v (Or.inr rfl)).mpr rfl

/-- 上升且首末两项都在该行存在时，复制块该位置精确是原值加次数乘截断差值。 -/
theorem copy_entry_shift_l (hℳ : Theory.Models ℳ theory_m)
    {C H L E B O U D : set_l ℳ}
    (hC : graph_semantics_l (graph_m copy_m) C)
    (hH : graph_semantics_l (graph_m head_m) H)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hB : graph_semantics_l (graph_m ascending_m) B)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hU : graph_semantics_l (graph_m SecondOrderProgramCopyOptional.update_m) U)
    (hD : graph_semantics_l (graph_m sub_m) D)
    {b A k l blk f : num_l ℳ} (hf : relation_l H b f)
    (hblk : relation_l C (value_l b (value_l A (value_l k l))) blk)
    {w j s n r v colj : num_l ℳ} (hw : relation_l L b w)
    (hj : SecondOrderOrder.lt_l j w)
    (hs : relation_l E (value_l b j) s) (hn : relation_l L s n)
    (hr : SecondOrderOrder.lt_l r n) (hv : relation_l E (value_l s r) v)
    (hcol : relation_l E (value_l blk j) colj)
    (hBz : ¬relation_l B (value_l A (value_l j r)) (zero_l ℳ))
    (fo la d : num_l ℳ) (hfo : relation_l O (value_l f r) (succ_l fo))
    (hla : relation_l O (value_l l r) (succ_l la)) (hd : relation_l D (value_l la fo) d) :
    relation_l E (value_l colj r) (add_l v (mul_l k d)) := by
  rw [copy_entry_value_l hℳ hC hH hL hE hB hO hU hf hblk hw hj hs hn hr hv colj _ hcol]
  refine Or.inr ⟨hBz, succ_l fo, succ_l la, hfo, hla, ?_⟩
  exact (SecondOrderProgramCopyOptional.update_some_l hℳ hU hD v k fo la _).mpr ⟨d, hd, rfl⟩

/-- 同一可选图上 `some 0` 的后继码与 `none` 的零码互斥，缺项判定不会被补零混淆。 -/
theorem optional_present_not_none_l (hℳ : Theory.Models ℳ theory_m) {O : set_l ℳ}
    (hO : graph_semantics_l (graph_m optional_m) O) (x c : num_l ℳ)
    (hx : relation_l O x (succ_l c)) : ¬relation_l O x (zero_l ℳ) :=
  fun h => nonzero_l hℳ c
    (function_value_unique_l (function_of_semantics_l hℳ optional_m hO) hx h)

/-- 同一分支公式对 `copies_m` 的真实输出成立：末尾第 `succ k` 份副本的块列在总输出
平坦列 `w·k + j` 处，其逐行读值与原块同位置的分支公式完全一致。 -/
theorem copies_entry_value_l (hℳ : Theory.Models ℳ theory_m)
    {R C H L E B O U : set_l ℳ}
    (hR : graph_semantics_l (graph_m copies_m) R)
    (hC : graph_semantics_l (graph_m copy_m) C)
    (hH : graph_semantics_l (graph_m head_m) H)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hB : graph_semantics_l (graph_m ascending_m) B)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hU : graph_semantics_l (graph_m SecondOrderProgramCopyOptional.update_m) U)
    {b A k l blk f : num_l ℳ} (hf : relation_l H b f)
    (hblk : relation_l C (value_l b (value_l A (value_l k l))) blk)
    {w j s n r v out colj e : num_l ℳ} (hw : relation_l L b w)
    (hy : relation_l R (value_l (value_l b (value_l A l)) (succ_l k)) out)
    (hj : SecondOrderOrder.lt_l j w) (hs : relation_l E (value_l b j) s)
    (hn : relation_l L s n) (hr : SecondOrderOrder.lt_l r n)
    (hv : relation_l E (value_l s r) v)
    (hcol : relation_l E (value_l out (add_l (mul_l w k) j)) colj) :
    relation_l E (value_l colj r) e ↔
      (relation_l B (value_l A (value_l j r)) (zero_l ℳ) ∧ v = e) ∨
        (¬relation_l B (value_l A (value_l j r)) (zero_l ℳ) ∧ ∃ first last,
          relation_l O (value_l f r) first ∧ relation_l O (value_l l r) last ∧
            relation_l U (value_l v (value_l k (value_l first last))) e) :=
  copy_entry_value_l hℳ hC hH hL hE hB hO hU hf hblk hw hj hs hn hr hv colj e
    ((block_read_last_l hℳ hR hC hL hE hw hblk hy hj colj).mp hcol)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyShiftEntry
