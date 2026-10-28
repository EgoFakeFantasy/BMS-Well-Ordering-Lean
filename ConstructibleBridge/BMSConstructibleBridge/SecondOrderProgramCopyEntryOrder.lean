import BMSConstructibleBridge.SecondOrderProgramAscendingAncestor
import BMSConstructibleBridge.SecondOrderProgramCopyRectangular
import BMSConstructibleBridge.SecondOrderProgramCopyShiftEntry
import BMSConstructibleBridge.SecondOrderProgramEntrySpecification
import BMSConstructibleBridge.SecondOrderProgramUniformParentComparison

/-!
# 单个副本中祖先相关列的条目序保持

若源块的两个局部列在给定行触发相同的上升分支，则 `copy_m` 对两项增加同一内部
偏移；若任一公共 Option 参数缺失，则两项都保持原值。因此两列真实 some 坐标的
严格序在源块与任意内部编号副本之间等价。矩形性只用于保证所讨论行确实有值。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyEntryOrder

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic
open SecondOrderProgramCopyBlock (copy_m)
open SecondOrderProgramCopyShiftEntry (copy_entry_asis_l copy_entry_shift_l)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListCode (head_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramAscending (ascending_m)
open SecondOrderProgramOptionalLookup (optional_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramUniformParentComparison (entry_order_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 矩形数组的真实 entry-some 关系可在有效列、有效行上消去为实际逐项读取。 -/
private theorem entry_value_l (hℳ : Theory.Models ℳ theory_m) {J O L E : set_l ℳ}
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x w h i r c a : num_l ℳ}
    (hx : rectangular_l L E x w h) (hi : SecondOrderOrder.lt_l i w)
    (hr : SecondOrderOrder.lt_l r h) (hc : relation_l E (value_l x i) c) :
    relation_l J (value_l x (value_l i r)) (succ_l a) ↔ relation_l E (value_l c r) a := by
  have hoc : relation_l O (value_l x i) (succ_l c) :=
    (SecondOrderProgramEntrySpecification.optional_some_l hℳ hO hL hE hx.1 i c).mpr ⟨hi, hc⟩
  rw [SecondOrderProgramEntrySpecification.entry_column_l hℳ hJ hO hoc,
    SecondOrderProgramEntrySpecification.optional_some_l hℳ hO hL hE (hx.2 i hi c hc)]
  simp only [hr, true_and]

/-- 同步上升分支下，源块与任意编号副本在这对列上的严格坐标比较完全一致。 -/
theorem entry_order_congr_l (hℳ : Theory.Models ℳ theory_m)
    {C H L E B O U D J : set_l ℳ}
    (hC : graph_semantics_l (graph_m copy_m) C)
    (hH : graph_semantics_l (graph_m head_m) H)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hB : graph_semantics_l (graph_m ascending_m) B)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hU : graph_semantics_l (graph_m SecondOrderProgramCopyOptional.update_m) U)
    (hD : graph_semantics_l (graph_m SecondOrderProgramSubtraction.sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    {b w h A k l blk f r i j : num_l ℳ}
    (hb : rectangular_l L E b w h) (hf : relation_l H b f)
    (hblk : relation_l C (value_l b (value_l A (value_l k l))) blk)
    (hr : SecondOrderOrder.lt_l r h) (hi : SecondOrderOrder.lt_l i w)
    (hj : SecondOrderOrder.lt_l j w)
    (hflag : relation_l B (value_l A (value_l i r)) (zero_l ℳ) ↔
      relation_l B (value_l A (value_l j r)) (zero_l ℳ)) :
    entry_order_l J b r i j ↔ entry_order_l J blk r i j := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  have hbr := SecondOrderProgramCopyRectangular.copy_rectangular_l hℳ hC hL hE hb hblk
  have hEf := function_of_semantics_l hℳ lookup_m hE
  obtain ⟨si, hsi, _⟩ := hEf (value_l b i)
  obtain ⟨sj, hsj, _⟩ := hEf (value_l b j)
  obtain ⟨ti, hti, _⟩ := hEf (value_l blk i)
  obtain ⟨tj, htj, _⟩ := hEf (value_l blk j)
  obtain ⟨vi, hvi, _⟩ := hEf (value_l si r)
  obtain ⟨vj, hvj, _⟩ := hEf (value_l sj r)
  have hsiL := hb.2 i hi si hsi
  have hsjL := hb.2 j hj sj hsj
  obtain ⟨s, his, hjs⟩ : ∃ s,
      relation_l E (value_l ti r) (add_l vi s) ∧
        relation_l E (value_l tj r) (add_l vj s) := by
    by_cases hzi : relation_l B (value_l A (value_l i r)) (zero_l ℳ)
    · have hzj := hflag.mp hzi
      have hei := copy_entry_asis_l hℳ hC hH hL hE hB hO hU hf hblk hb.1 hi hsi hsiL
        hr hvi hti (Or.inl hzi)
      have hej := copy_entry_asis_l hℳ hC hH hL hE hB hO hU hf hblk hb.1 hj hsj hsjL
        hr hvj htj (Or.inl hzj)
      refine ⟨zero_l ℳ, ?_, ?_⟩
      · simpa only [add_zero_l hℳ] using hei
      · simpa only [add_zero_l hℳ] using hej
    · have hzj : ¬relation_l B (value_l A (value_l j r)) (zero_l ℳ) :=
        fun h => hzi (hflag.mpr h)
      have hOf := function_of_semantics_l hℳ optional_m hO
      obtain ⟨fo, hfo, _⟩ := hOf (value_l f r)
      obtain ⟨la, hla, _⟩ := hOf (value_l l r)
      by_cases hzero : fo = zero_l ℳ ∨ la = zero_l ℳ
      · have hei := copy_entry_asis_l hℳ hC hH hL hE hB hO hU hf hblk hb.1 hi hsi hsiL
          hr hvi hti (Or.inr ⟨fo, la, hfo, hla, hzero⟩)
        have hej := copy_entry_asis_l hℳ hC hH hL hE hB hO hU hf hblk hb.1 hj hsj hsjL
          hr hvj htj (Or.inr ⟨fo, la, hfo, hla, hzero⟩)
        refine ⟨zero_l ℳ, ?_, ?_⟩
        · simpa only [add_zero_l hℳ] using hei
        · simpa only [add_zero_l hℳ] using hej
      · rcases predecessor_l hℳ fo with rfl | ⟨fo', rfl⟩
        · exact False.elim (hzero (Or.inl rfl))
        · rcases predecessor_l hℳ la with rfl | ⟨la', rfl⟩
          · exact False.elim (hzero (Or.inr rfl))
          · obtain ⟨d, hd, _⟩ := function_of_semantics_l hℳ
              SecondOrderProgramSubtraction.sub_m hD (value_l la' fo')
            exact ⟨mul_l k d,
              copy_entry_shift_l hℳ hC hH hL hE hB hO hU hD hf hblk hb.1 hi hsi hsiL
                hr hvi hti hzi fo' la' d hfo hla hd,
              copy_entry_shift_l hℳ hC hH hL hE hB hO hU hD hf hblk hb.1 hj hsj hsjL
                hr hvj htj hzj fo' la' d hfo hla hd⟩
  have hbi (a : num_l ℳ) := entry_value_l hℳ hJ hO hL hE hb hi hr hsi (a := a)
  have hbj (a : num_l ℳ) := entry_value_l hℳ hJ hO hL hE hb hj hr hsj (a := a)
  have hki (a : num_l ℳ) := entry_value_l hℳ hJ hO hL hE hbr hi hr hti (a := a)
  have hkj (a : num_l ℳ) := entry_value_l hℳ hJ hO hL hE hbr hj hr htj (a := a)
  constructor
  · rintro ⟨a, d, hai, hjd, had⟩
    have hav : a = vi := function_value_unique_l hEf ((hbi a).mp hai) hvi
    have hdv : d = vj := function_value_unique_l hEf ((hbj d).mp hjd) hvj
    subst a
    subst d
    exact ⟨add_l vi s, add_l vj s, (hki _).mpr his, (hkj _).mpr hjs,
      add_lt_add_left had s⟩
  · rintro ⟨a, d, hai, hjd, had⟩
    have hav : a = add_l vi s := function_value_unique_l hEf ((hki a).mp hai) his
    have hdv : d = add_l vj s := function_value_unique_l hEf ((hkj d).mp hjd) hjs
    subst a
    subst d
    exact ⟨vi, vj, (hbi _).mpr hvi, (hbj _).mpr hvj, (add_lt_add_iff_right s).mp had⟩

/-- 零上升标记时，不同复制编号产生的块在该局部坐标保留同一条目。 -/
theorem entry_value_congr_of_zero_l (hℳ : Theory.Models ℳ theory_m)
    {C H L E B O U J : set_l ℳ}
    (hC : graph_semantics_l (graph_m copy_m) C)
    (hH : graph_semantics_l (graph_m head_m) H)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hB : graph_semantics_l (graph_m ascending_m) B)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hU : graph_semantics_l (graph_m SecondOrderProgramCopyOptional.update_m) U)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    {b w h A k₁ l₁ blk₁ k₂ l₂ blk₂ f i r q : num_l ℳ}
    (hb : rectangular_l L E b w h) (hf : relation_l H b f)
    (hblk₁ : relation_l C (value_l b (value_l A (value_l k₁ l₁))) blk₁)
    (hblk₂ : relation_l C (value_l b (value_l A (value_l k₂ l₂))) blk₂)
    (hi : SecondOrderOrder.lt_l i w) (hr : SecondOrderOrder.lt_l r h)
    (hzero : relation_l B (value_l A (value_l i r)) (zero_l ℳ)) :
    relation_l J (value_l blk₁ (value_l i r)) (succ_l q) ↔
      relation_l J (value_l blk₂ (value_l i r)) (succ_l q) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  have hrect₁ := SecondOrderProgramCopyRectangular.copy_rectangular_l
    hℳ hC hL hE hb hblk₁
  have hrect₂ := SecondOrderProgramCopyRectangular.copy_rectangular_l
    hℳ hC hL hE hb hblk₂
  obtain ⟨s, hs, _⟩ := function_of_semantics_l hℳ lookup_m hE (value_l b i)
  obtain ⟨col₁, hcol₁, _⟩ := function_of_semantics_l hℳ lookup_m hE (value_l blk₁ i)
  obtain ⟨col₂, hcol₂, _⟩ := function_of_semantics_l hℳ lookup_m hE (value_l blk₂ i)
  obtain ⟨v, hv, _⟩ := function_of_semantics_l hℳ lookup_m hE (value_l s r)
  have hsL := hb.2 i hi s hs
  have hv₁ := copy_entry_asis_l hℳ hC hH hL hE hB hO hU hf hblk₁
    hb.1 hi hs hsL hr hv hcol₁ (Or.inl hzero)
  have hv₂ := copy_entry_asis_l hℳ hC hH hL hE hB hO hU hf hblk₂
    hb.1 hi hs hsL hr hv hcol₂ (Or.inl hzero)
  have hEf := function_of_semantics_l hℳ lookup_m hE
  have hentry₁ (a : num_l ℳ) := entry_value_l hℳ hJ hO hL hE hrect₁ hi hr hcol₁ (a := a)
  have hentry₂ (a : num_l ℳ) := entry_value_l hℳ hJ hO hL hE hrect₂ hi hr hcol₂ (a := a)
  constructor
  · intro h
    have hqv : q = v := function_value_unique_l hEf ((hentry₁ q).mp h) hv₁
    exact (hentry₂ q).mpr (by simpa [hqv] using hv₂)
  · intro h
    have hqv : q = v := function_value_unique_l hEf ((hentry₂ q).mp h) hv₂
    exact (hentry₁ q).mpr (by simpa [hqv] using hv₁)

/-- 零上升标记时，两份复制块在该坐标都有同一个实际条目值。 -/
theorem entry_value_common_of_zero_l (hℳ : Theory.Models ℳ theory_m)
    {C H L E B O U J : set_l ℳ}
    (hC : graph_semantics_l (graph_m copy_m) C)
    (hH : graph_semantics_l (graph_m head_m) H)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hB : graph_semantics_l (graph_m ascending_m) B)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hU : graph_semantics_l (graph_m SecondOrderProgramCopyOptional.update_m) U)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    {b w h A k₁ l₁ blk₁ k₂ l₂ blk₂ f i r : num_l ℳ}
    (hb : rectangular_l L E b w h) (hf : relation_l H b f)
    (hblk₁ : relation_l C (value_l b (value_l A (value_l k₁ l₁))) blk₁)
    (hblk₂ : relation_l C (value_l b (value_l A (value_l k₂ l₂))) blk₂)
    (hi : SecondOrderOrder.lt_l i w) (hr : SecondOrderOrder.lt_l r h)
    (hzero : relation_l B (value_l A (value_l i r)) (zero_l ℳ)) :
    ∃ v, relation_l J (value_l blk₁ (value_l i r)) (succ_l v) ∧
      relation_l J (value_l blk₂ (value_l i r)) (succ_l v) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  have hrect₁ := SecondOrderProgramCopyRectangular.copy_rectangular_l
    hℳ hC hL hE hb hblk₁
  have hrect₂ := SecondOrderProgramCopyRectangular.copy_rectangular_l
    hℳ hC hL hE hb hblk₂
  obtain ⟨s, hs, _⟩ := function_of_semantics_l hℳ lookup_m hE (value_l b i)
  obtain ⟨col₁, hcol₁, _⟩ := function_of_semantics_l hℳ lookup_m hE (value_l blk₁ i)
  obtain ⟨col₂, hcol₂, _⟩ := function_of_semantics_l hℳ lookup_m hE (value_l blk₂ i)
  obtain ⟨v, hv, _⟩ := function_of_semantics_l hℳ lookup_m hE (value_l s r)
  have hsL := hb.2 i hi s hs
  have hv₁ := copy_entry_asis_l hℳ hC hH hL hE hB hO hU hf hblk₁
    hb.1 hi hs hsL hr hv hcol₁ (Or.inl hzero)
  have hv₂ := copy_entry_asis_l hℳ hC hH hL hE hB hO hU hf hblk₂
    hb.1 hi hs hsL hr hv hcol₂ (Or.inl hzero)
  exact ⟨v,
    (entry_value_l hℳ hJ hO hL hE hrect₁ hi hr hcol₁).mpr hv₁,
    (entry_value_l hℳ hJ hO hL hE hrect₂ hi hr hcol₂).mpr hv₂⟩

/-- 若右列不平移，则副本中的严格比较必已在源块中成立；左列可能增加非负偏移。 -/
theorem entry_order_of_copy_right_zero_l (hℳ : Theory.Models ℳ theory_m)
    {C H L E B O U D J : set_l ℳ}
    (hC : graph_semantics_l (graph_m copy_m) C)
    (hH : graph_semantics_l (graph_m head_m) H)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hB : graph_semantics_l (graph_m ascending_m) B)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hU : graph_semantics_l (graph_m SecondOrderProgramCopyOptional.update_m) U)
    (hD : graph_semantics_l (graph_m SecondOrderProgramSubtraction.sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    {b w h A k l blk f r i j : num_l ℳ}
    (hb : rectangular_l L E b w h) (hf : relation_l H b f)
    (hblk : relation_l C (value_l b (value_l A (value_l k l))) blk)
    (hr : SecondOrderOrder.lt_l r h) (hi : SecondOrderOrder.lt_l i w)
    (hj : SecondOrderOrder.lt_l j w)
    (hzj : relation_l B (value_l A (value_l j r)) (zero_l ℳ)) :
    entry_order_l J blk r i j → entry_order_l J b r i j := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  have hbr := SecondOrderProgramCopyRectangular.copy_rectangular_l hℳ hC hL hE hb hblk
  have hEf := function_of_semantics_l hℳ lookup_m hE
  obtain ⟨si, hsi, _⟩ := hEf (value_l b i)
  obtain ⟨sj, hsj, _⟩ := hEf (value_l b j)
  obtain ⟨ti, hti, _⟩ := hEf (value_l blk i)
  obtain ⟨tj, htj, _⟩ := hEf (value_l blk j)
  obtain ⟨vi, hvi, _⟩ := hEf (value_l si r)
  obtain ⟨vj, hvj, _⟩ := hEf (value_l sj r)
  have hsiL := hb.2 i hi si hsi
  have hsjL := hb.2 j hj sj hsj
  have hjs : relation_l E (value_l tj r) vj :=
    copy_entry_asis_l hℳ hC hH hL hE hB hO hU hf hblk hb.1 hj hsj hsjL
      hr hvj htj (Or.inl hzj)
  obtain ⟨s, his⟩ : ∃ s, relation_l E (value_l ti r) (add_l vi s) := by
    by_cases hzi : relation_l B (value_l A (value_l i r)) (zero_l ℳ)
    · refine ⟨zero_l ℳ, ?_⟩
      simpa only [add_zero_l hℳ] using
        (copy_entry_asis_l hℳ hC hH hL hE hB hO hU hf hblk hb.1 hi hsi hsiL
          hr hvi hti (Or.inl hzi))
    · have hOf := function_of_semantics_l hℳ optional_m hO
      obtain ⟨fo, hfo, _⟩ := hOf (value_l f r)
      obtain ⟨la, hla, _⟩ := hOf (value_l l r)
      by_cases hzero : fo = zero_l ℳ ∨ la = zero_l ℳ
      · refine ⟨zero_l ℳ, ?_⟩
        simpa only [add_zero_l hℳ] using
          (copy_entry_asis_l hℳ hC hH hL hE hB hO hU hf hblk hb.1 hi hsi hsiL
            hr hvi hti (Or.inr ⟨fo, la, hfo, hla, hzero⟩))
      · rcases predecessor_l hℳ fo with rfl | ⟨fo', rfl⟩
        · exact False.elim (hzero (Or.inl rfl))
        · rcases predecessor_l hℳ la with rfl | ⟨la', rfl⟩
          · exact False.elim (hzero (Or.inr rfl))
          · obtain ⟨d, hd, _⟩ := function_of_semantics_l hℳ
              SecondOrderProgramSubtraction.sub_m hD (value_l la' fo')
            exact ⟨mul_l k d,
              copy_entry_shift_l hℳ hC hH hL hE hB hO hU hD hf hblk hb.1 hi hsi hsiL
                hr hvi hti hzi fo' la' d hfo hla hd⟩
  have hbi (a : num_l ℳ) := entry_value_l hℳ hJ hO hL hE hb hi hr hsi (a := a)
  have hbj (a : num_l ℳ) := entry_value_l hℳ hJ hO hL hE hb hj hr hsj (a := a)
  have hki (a : num_l ℳ) := entry_value_l hℳ hJ hO hL hE hbr hi hr hti (a := a)
  have hkj (a : num_l ℳ) := entry_value_l hℳ hJ hO hL hE hbr hj hr htj (a := a)
  rintro ⟨a, d, hai, hjd, had⟩
  have hav : a = add_l vi s := function_value_unique_l hEf ((hki a).mp hai) his
  have hdv : d = vj := function_value_unique_l hEf ((hkj d).mp hjd) hjs
  subst a
  subst d
  exact ⟨vi, vj, (hbi _).mpr hvi, (hbj _).mpr hvj,
    lt_of_le_of_lt (le_add_of_nonneg_right (zero_le_l hℳ s)) had⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyEntryOrder
