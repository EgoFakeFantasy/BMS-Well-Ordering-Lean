import BMSConstructibleBridge.SecondOrderProgramCopyZeroEntry
import BMSConstructibleBridge.SecondOrderProgramCopyBlockLookup
import BMSConstructibleBridge.SecondOrderProgramCopyBlockShape
import BMSConstructibleBridge.SecondOrderProgramListExtensionality

/-!
# 原零号坏块副本与原块编码相同

先确认共享参数确由原块头生成，再用两层原映射的逐下标规格及已验内部列表外延性。
结论是原编码相等，而非仅长度或外部标准读值相同；不要求矩形性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyZero

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramValue SecondOrderProgramCallbackValue
open SecondOrderProgramCopyBlock (parameter_m column_m copy_m)
open SecondOrderProgramCopyBlockShape (column_length_l copy_width_l)
open SecondOrderProgramCopyBlockLookup (column_entry_l copy_column_l)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramListCode (head_m)
open SecondOrderProgramListExtensionality (extensionality_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原共享参数读取同一块头，不允许调用方任意替换首列。 -/
theorem parameter_l (hℳ : Theory.Models ℳ theory_m) {P H : set_l ℳ}
    (hP : graph_semantics_l (graph_m parameter_m) P)
    (hH : graph_semantics_l (graph_m head_m) H) {b f : num_l ℳ}
    (hb : relation_l H b f) (A k l q : num_l ℳ) :
    relation_l P (value_l b (value_l A (value_l k l))) q ↔
      value_l A (value_l k (value_l f l)) = q := by
  obtain ⟨g, hg, _⟩ := value_exists_l hℳ head_m hH
  have hgf := (hg hH b f).mp hb
  have hv : value_spec_l parameter_m _ := pair_value_l hℳ
    (comp_value_l hℳ (left_value_l hℳ) (right_value_l hℳ))
    (pair_value_l hℳ
      (comp_value_l hℳ (comp_value_l hℳ (left_value_l hℳ) (right_value_l hℳ)) (right_value_l hℳ))
      (pair_value_l hℳ (comp_value_l hℳ hg (left_value_l hℳ))
        (comp_value_l hℳ (comp_value_l hℳ (right_value_l hℳ) (right_value_l hℳ)) (right_value_l hℳ))))
  simpa only [SecondOrderUnpairing.unpair_l, hgf] using
    hv hP (value_l b (value_l A (value_l k l))) q

/-- 原内层列映射在复制指标零时返回同一列码，覆盖内部非标准长度。 -/
theorem column_zero_l (hℳ : Theory.Models ℳ theory_m) {C : set_l ℳ}
    (hC : graph_semantics_l (graph_m column_m) C) (A f l j s y : num_l ℳ) :
    relation_l C (value_l (value_l A (value_l (zero_l ℳ) (value_l f l))) (value_l j s)) y ↔
      s = y := by
  obtain ⟨L, hLf, hL⟩ := graph_total_l hℳ length_m
  obtain ⟨E, _, hE⟩ := graph_total_l hℳ lookup_m
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ SecondOrderProgramCopyEntry.entry_m
  obtain ⟨n, hn, _⟩ := hLf s
  have hCf := function_of_semantics_l hℳ column_m hC
  obtain ⟨z, hz, _⟩ := hCf
    (value_l (value_l A (value_l (zero_l ℳ) (value_l f l))) (value_l j s))
  have hsz : s = z := by
    apply extensionality_l hℳ hL hE hn (column_length_l hℳ hC hL hz hn)
    intro i hi a ha
    exact (column_entry_l hℳ hC hR hL hE hz hn hi ha).mpr
      ((SecondOrderProgramCopyZeroEntry.entry_zero_l hℳ hR A f l j i a a).mpr rfl)
  rw [← hsz] at hz
  exact ⟨fun hy => function_value_unique_l hCf hz hy, fun hy => hy ▸ hz⟩

/-- 单个原copyBlock在复制指标零时精确返回原块码，首列仍从该块读取。 -/
theorem copy_zero_l (hℳ : Theory.Models ℳ theory_m) {C : set_l ℳ}
    (hC : graph_semantics_l (graph_m copy_m) C) (b A l y : num_l ℳ) :
    relation_l C (value_l b (value_l A (value_l (zero_l ℳ) l))) y ↔ b = y := by
  obtain ⟨L, hLf, hL⟩ := graph_total_l hℳ length_m
  obtain ⟨E, _, hE⟩ := graph_total_l hℳ lookup_m
  obtain ⟨K, _, hK⟩ := graph_total_l hℳ column_m
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ parameter_m
  obtain ⟨H, hHf, hH⟩ := graph_total_l hℳ head_m
  obtain ⟨f, hf, _⟩ := hHf b
  obtain ⟨n, hn, _⟩ := hLf b
  have hp := (parameter_l hℳ hP hH hf A (zero_l ℳ) l _).mpr rfl
  have hCf := function_of_semantics_l hℳ copy_m hC
  obtain ⟨z, hz, _⟩ := hCf (value_l b (value_l A (value_l (zero_l ℳ) l)))
  have hbz : b = z := by
    apply extensionality_l hℳ hL hE hn (copy_width_l hℳ hC hL hz hn)
    intro j hj s hs
    exact (copy_column_l hℳ hC hK hP hL hE hz hp hn hj hs).mpr
      ((column_zero_l hℳ hK A f l j s s).mpr rfl)
  rw [← hbz] at hz
  exact ⟨fun hy => function_value_unique_l hCf hz hy, fun hy => hy ▸ hz⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyZero
