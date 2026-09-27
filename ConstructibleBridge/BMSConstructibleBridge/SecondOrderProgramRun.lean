import BMSConstructibleBridge.SecondOrderProgramExpansion
import BMSConstructibleBridge.ArithmeticPresentation

/-!
# 原有限展开轨迹的程序

输入pair轨迹码数组码，左折叠的回调恰好需要pair当前数组展开指标，故直接使用已验
expand_m，没有反转轨迹或重排展开次序。标准端连接原ArithmeticPresentation.run_l，
内部端复用真实fold图在任意内部头、尾、初值上的递推式。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramRun

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderProgramSemantics
open SecondOrderProgramListFold
open SecondOrderProgramExpansion (expand_m expand_encode_l)
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 沿输入轨迹从左到右执行同一原展开程序。 -/
def run_m : code_m := fold_m expand_m

private theorem fold_raw_l (s : List Nat) (a : ValidArray) :
    s.foldl (fun w i => eval_l expand_m (Nat.pair w i)) (Encodable.encode a.raw) =
      Encodable.encode (ArithmeticPresentation.run_l a s).raw := by
  induction s generalizing a with
  | nil => rfl
  | cons i s ih =>
      rw [List.foldl_cons, expand_encode_l]
      exact ih (a.expand i)

/-- 精确原轨迹身份；起点可为任意合法数组，不另加生成性假设。 -/
theorem run_encode_l (a : ValidArray) (s : List Nat) :
    eval_l run_m (Nat.pair (Encodable.encode s) (Encodable.encode a.raw)) =
      Encodable.encode (ArithmeticPresentation.run_l a s).raw := by
  rw [run_m, fold_encode_l]
  exact fold_raw_l s a

/-- 内部空轨迹不改变初值。 -/
theorem run_zero_l (hℳ : Theory.Models ℳ theory_m) {R : set_l ℳ}
    (hR : graph_semantics_l (graph_m run_m) R) (v y : num_l ℳ) :
    relation_l R (value_l (zero_l ℳ) v) y ↔ v = y :=
  fold_zero_l hℳ expand_m hR v y

/-- 内部非空轨迹先执行首指标，再执行尾轨迹；原实际展开图仍是前件。 -/
theorem run_cons_l (hℳ : Theory.Models ℳ theory_m) {R E : set_l ℳ}
    (hR : graph_semantics_l (graph_m run_m) R)
    (hE : graph_semantics_l (graph_m expand_m) E) (i t v y : num_l ℳ) :
    relation_l R (value_l (succ_l (value_l i t)) v) y ↔
      ∃ w, relation_l E (value_l v i) w ∧ relation_l R (value_l t w) y :=
  fold_cons_l hℳ expand_m hR hE i t v y

#print axioms run_m
#print axioms run_encode_l
#print axioms run_zero_l
#print axioms run_cons_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramRun
