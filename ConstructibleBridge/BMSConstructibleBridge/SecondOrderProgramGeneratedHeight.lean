import BMSConstructibleBridge.SecondOrderProgramGeneratedDecode
import BMSConstructibleBridge.SecondOrderRawHeightFormula

/-!
# 原生成数组当前高度与内部尾部行

在原轨迹解码程序后接原裁剪高度程序。上界模板现在实际作用于生成轨迹码，
再通过同一解码图约束其输出数组的全部内部尾部行；不再仅处理裸数组码。
此结论不约束种子高度、历史中间高度、轨迹长度或数组宽度。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramGeneratedHeight

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramValue SecondOrderProgramCallbackValue
open SecondOrderProgramArithmetic
open SecondOrderProgramGeneratedDecode (decode_m decode_eval_l)
open SecondOrderProgramTrimHeight (trim_m trim_encode_l)
open SecondOrderProgramZeroRows (zero_rows_l trim_bound_iff_zero_rows_l)
open SecondOrderProgramListLookup (lookup_m)
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原生成轨迹解码后的当前裁剪高度。 -/
def height_m : code_m := .comp trim_m decode_m

/-- 逐自然数身份连接原HeightDescent高度，不连接初始种子高度。 -/
theorem height_eval_l (x : Nat) :
    eval_l height_m x = HeightDescent.height_l (ArithmeticPresentation.decode_l x).1 := by
  change eval_l trim_m (eval_l decode_m x) = _
  rw [decode_eval_l, trim_encode_l]
  rfl

/-- 任意内部码的高度图先运行同一解码图，再读取同一裁剪高度图。 -/
theorem height_rel_l (hℳ : Theory.Models ℳ theory_m) {H D T : set_l ℳ}
    (hH : graph_semantics_l (graph_m height_m) H)
    (hD : graph_semantics_l (graph_m decode_m) D)
    (hT : graph_semantics_l (graph_m trim_m) T) (x y : num_l ℳ) :
    relation_l H x y ↔ ∃ a, relation_l D x a ∧ relation_l T a y :=
  comp_rel_l hℳ (graph_m trim_m) (graph_m decode_m) T D hT hD hH x y

/-- 已知实际内部解码输出时，原高度模板等价于该数组全部尾部行读零。 -/
theorem bound_decoded_l (hℳ : Theory.Models ℳ theory_m) {D E : set_l ℳ}
    (hD : graph_semantics_l (graph_m decode_m) D)
    (hE : graph_semantics_l (graph_m lookup_m) E) {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (a b : Term signature_m Γ Δ .num) {x : num_l ℳ}
    (hx : relation_l D (a.eval η) x) :
    Formula.satisfies η (FixedHeightPureFormula.bound (graph_m height_m) a b) ↔
      zero_rows_l E x (b.eval η) := by
  obtain ⟨H, _, hH⟩ := graph_total_l hℳ height_m
  obtain ⟨T, hTf, hT⟩ := graph_total_l hℳ trim_m
  obtain ⟨y, hy, _⟩ := hTf x
  have hh := (height_rel_l hℳ hH hD hT (a.eval η) y).mpr ⟨x, hx, hy⟩
  exact (SecondOrderRawHeightFormula.bound_value_l hℳ height_m hH η a b hh).trans
    (trim_bound_iff_zero_rows_l hℳ hT hE hy (b.eval η))

/-- 不预给输出时，由同一解码图的总性取输出，保留原高度模板的双向含义。 -/
theorem bound_rel_l (hℳ : Theory.Models ℳ theory_m) {D E : set_l ℳ}
    (hD : graph_semantics_l (graph_m decode_m) D)
    (hE : graph_semantics_l (graph_m lookup_m) E) {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (a b : Term signature_m Γ Δ .num) :
    Formula.satisfies η (FixedHeightPureFormula.bound (graph_m height_m) a b) ↔
      ∃ x, relation_l D (a.eval η) x ∧ zero_rows_l E x (b.eval η) := by
  constructor
  · intro hb
    obtain ⟨x, hx, _⟩ := function_of_semantics_l hℳ decode_m hD (a.eval η)
    exact ⟨x, hx, (bound_decoded_l hℳ hD hE η a b hx).mp hb⟩
  · rintro ⟨x, hx, hz⟩
    exact (bound_decoded_l hℳ hD hE η a b hx).mpr hz

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramGeneratedHeight
