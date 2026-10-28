import BMSConstructibleBridge.SecondOrderProgramCopyRectangular
import BMSConstructibleBridge.SecondOrderProgramCopyShiftEntry
import BMSConstructibleBridge.SecondOrderProgramEntrySpecification

/-!
# 复制块真实存在条目的数值公式

把逐列表的 `lookup_m` 数值公式提升为 `entry_m` 的 some 坐标公式。
所有存在性来自原矩形数组及真实复制输出；缺项分支不在本定理的前提中。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyShiftEntrySome

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramCopyBlock (copy_m)
open SecondOrderProgramListCode (head_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramAscending (ascending_m)
open SecondOrderProgramOptionalLookup (optional_m)
open SecondOrderProgramSubtraction (sub_m)
open SecondOrderProgramEntry (entry_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 真实上升分支的源 some 坐标在第 `k` 个副本中精确增加 `k·gap`。 -/
theorem entry_shift_l (hℳ : Theory.Models ℳ theory_m)
    {C H L E B O U D J : set_l ℳ}
    (hC : graph_semantics_l (graph_m copy_m) C)
    (hH : graph_semantics_l (graph_m head_m) H)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hB : graph_semantics_l (graph_m ascending_m) B)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hU : graph_semantics_l (graph_m SecondOrderProgramCopyOptional.update_m) U)
    (hD : graph_semantics_l (graph_m sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    {b w height A k l blk f r i v fo la gap : num_l ℳ}
    (hb : rectangular_l L E b w height)
    (hf : relation_l H b f)
    (hblk : relation_l C (value_l b (value_l A (value_l k l))) blk)
    (hr : SecondOrderOrder.lt_l r height)
    (hi : SecondOrderOrder.lt_l i w)
    (hsource : relation_l J (value_l b (value_l i r)) (succ_l v))
    (hflag : ¬relation_l B (value_l A (value_l i r)) (zero_l ℳ))
    (hfo : relation_l O (value_l f r) (succ_l fo))
    (hla : relation_l O (value_l l r) (succ_l la))
    (hgap : relation_l D (value_l la fo) gap) :
    relation_l J (value_l blk (value_l i r))
      (succ_l (add_l v (mul_l k gap))) := by
  have hbr := SecondOrderProgramCopyRectangular.copy_rectangular_l hℳ hC hL hE hb hblk
  have hEf := function_of_semantics_l hℳ lookup_m hE
  obtain ⟨s, hs, _⟩ := hEf (value_l b i)
  obtain ⟨col, hcol, _⟩ := hEf (value_l blk i)
  have hso := (SecondOrderProgramEntrySpecification.optional_some_l
    hℳ hO hL hE hb.1 i s).mpr ⟨hi, hs⟩
  have hvo := (SecondOrderProgramEntrySpecification.entry_column_l hℳ hJ hO hso
    r (succ_l v)).mp
    hsource
  have hv := ((SecondOrderProgramEntrySpecification.optional_some_l hℳ hO hL hE
    (hb.2 i hi s hs) r v).mp hvo).2
  have hshift := SecondOrderProgramCopyShiftEntry.copy_entry_shift_l
    hℳ hC hH hL hE hB hO hU hD hf hblk hb.1 hi hs (hb.2 i hi s hs)
      hr hv hcol hflag fo la gap hfo hla hgap
  have hto := (SecondOrderProgramEntrySpecification.optional_some_l
    hℳ hO hL hE hbr.1 i col).mpr ⟨hi, hcol⟩
  apply (SecondOrderProgramEntrySpecification.entry_column_l hℳ hJ hO hto
    r (succ_l (add_l v (mul_l k gap)))).mpr
  exact (SecondOrderProgramEntrySpecification.optional_some_l hℳ hO hL hE
    (hbr.2 i hi col hcol) r (add_l v (mul_l k gap))).mpr ⟨hr, hshift⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyShiftEntrySome
