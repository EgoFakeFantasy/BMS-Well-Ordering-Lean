import BMSConstructibleBridge.SecondOrderProgramListCode

/-!
# 原七构造程序的非零指示器

零步返回零，后继步返回固定数码一。原递归方程与模型的零／后继分解足以给出
所有内部输入的规格；没有对内部数作外部自然数归纳，也没有增加判断或最小化指令。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramNonzero

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramRecurrence SecondOrderProgramListCode
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 零步为零、所有后继步为一的原递归程序。 -/
def nonzero_rec_m : code_m := .prec .zero (PrimitiveProgram.const_m 1)

/-- 输入配成 `pair 0 x`，得到原七构造中的一元非零指示器。 -/
def nonzero_m : code_m := .comp nonzero_rec_m pred_input_m

/-- 标准输入上的算法身份；不以此替代非标准内部规格。 -/
theorem nonzero_eval_l (n : Nat) : eval_l nonzero_m n = if n = 0 then 0 else 1 := by
  change eval_l nonzero_rec_m (Nat.pair 0 (eval_l PrimitiveProgram.id_m n)) = _
  rw [PrimitiveProgram.id_l, nonzero_rec_m, PrimitiveProgram.prec_l]
  cases n with
  | zero => rfl
  | succ n =>
      simp only [PrimitiveHistory.run_l, PrimitiveProgram.const_l, Nat.succ_ne_zero, ↓reduceIte]

/-- 原递归图在零步返回零。 -/
theorem rec_zero_l (hℳ : Theory.Models ℳ theory_m) {R : set_l ℳ}
    (hR : graph_semantics_l (graph_m nonzero_rec_m) R) (x y : num_l ℳ) :
    relation_l R (value_l x (zero_l ℳ)) y ↔ zero_l ℳ = y := by
  obtain ⟨Z, _, hZ⟩ := graph_total_l hℳ .zero
  obtain ⟨C, _, hC⟩ := graph_total_l hℳ (PrimitiveProgram.const_m 1)
  rw [prec_graph_zero_l hℳ (graph_m .zero) (graph_m (PrimitiveProgram.const_m 1))
    Z C hZ hC R hR, zero_rel_l hℳ hZ]

/-- 原递归图在任意内部后继步返回同一个数码一。 -/
theorem rec_succ_l (hℳ : Theory.Models ℳ theory_m) {R : set_l ℳ}
    (hR : graph_semantics_l (graph_m nonzero_rec_m) R) (x k y : num_l ℳ) :
    relation_l R (value_l x (succ_l k)) y ↔ y = numeral_val_l 1 := by
  obtain ⟨Z, hZf, hZ⟩ := graph_total_l hℳ .zero
  obtain ⟨C, hCf, hC⟩ := graph_total_l hℳ (PrimitiveProgram.const_m 1)
  rw [prec_graph_succ_l hℳ (graph_m .zero) (graph_m (PrimitiveProgram.const_m 1))
    Z C hZ hC R hR hZf hCf]
  constructor
  · rintro ⟨v, _, hv⟩
    exact (const_spec_l hℳ 1 hC _ y).mp hv
  · intro hy
    obtain ⟨v, hv, _⟩ := function_of_semantics_l hℳ nonzero_rec_m hR (value_l x k)
    exact ⟨v, hv, (const_spec_l hℳ 1 hC _ y).mpr hy⟩

/-- 一元程序与原递归图的逐点输入桥。 -/
theorem bridge_l (hℳ : Theory.Models ℳ theory_m) {R N : set_l ℳ}
    (hR : graph_semantics_l (graph_m nonzero_rec_m) R)
    (hN : graph_semantics_l (graph_m nonzero_m) N) (x y : num_l ℳ) :
    relation_l N x y ↔ relation_l R (value_l (zero_l ℳ) x) y := by
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ pred_input_m
  rw [comp_rel_l hℳ (graph_m nonzero_rec_m) (graph_m pred_input_m) R D hR hD hN]
  simp only [pred_input_rel_l hℳ hD, exists_eq_left']

/-- 零输入输出零。 -/
theorem zero_l (hℳ : Theory.Models ℳ theory_m) {N : set_l ℳ}
    (hN : graph_semantics_l (graph_m nonzero_m) N) (y : num_l ℳ) :
    relation_l N (SecondOrderModel.zero_l ℳ) y ↔ SecondOrderModel.zero_l ℳ = y := by
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ nonzero_rec_m
  rw [bridge_l hℳ hR hN, rec_zero_l hℳ hR]

/-- 任意非零内部输入输出一，不要求输入是某个外部数码。 -/
theorem positive_l (hℳ : Theory.Models ℳ theory_m) {N : set_l ℳ}
    (hN : graph_semantics_l (graph_m nonzero_m) N) {x : num_l ℳ}
    (hx : x ≠ SecondOrderModel.zero_l ℳ) (y : num_l ℳ) :
    relation_l N x y ↔ y = numeral_val_l 1 := by
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ nonzero_rec_m
  obtain ⟨k, rfl⟩ := (predecessor_l hℳ x).resolve_left hx
  rw [bridge_l hℳ hR hN, rec_succ_l hℳ hR]

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramNonzero
