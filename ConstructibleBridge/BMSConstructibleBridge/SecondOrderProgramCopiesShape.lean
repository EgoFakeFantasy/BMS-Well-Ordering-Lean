import BMSConstructibleBridge.SecondOrderProgramCopies
import BMSConstructibleBridge.SecondOrderProgramCopyBlockShape
import BMSConstructibleBridge.SecondOrderProgramListShift

/-!
# 原多副本程序的内部宽度

每个副本与固定原坏块等宽，逐次拼接后宽度恰为原块宽乘内部复制次数。
实际乘积宽度公式作为归纳正文，复制次数不要求是标准数，原块也不被累计块替换。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopiesShape

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic
open SecondOrderProgramCopies (copies_m copies_zero_l copies_succ_l)
open SecondOrderProgramCopyBlock (copy_m)
open SecondOrderProgramListAppend (append_m append_length_l)
open SecondOrderProgramLength (length_m length_rel_l)
open SecondOrderProgramListLength (length_zero_l)
open SecondOrderProgramListIteration (iterate_m)
open SecondOrderProgramListShift (output_m output_syntax_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 自由槽[复制次数n,固定参数q,块宽w,R,L]；绑定实际输出y。 -/
def width_m : Formula signature_m [] [.num, .num, .num, .set, .set] :=
  .existsE .num (.conj
    (output_m (.fvar (.there (.there (.there .here)))) (.fvar (.there .here)) (.fvar .here) (.bvar .here))
    (GraphSyntax.edge_m (.fvar (.there (.there (.there (.there .here))))) (.bvar .here)
      (Term.app (σ := signature_m) .mul (.cons (.fvar (.there (.there .here))) (.cons (.fvar .here) .nil)))))

/-- 乘积宽度公式仍在原纯语言中。 -/
theorem width_language_m : language_m width_m = true := pure_language_m _ rfl

/-- 公式精确表示原多副本图中某个输出具有该乘积宽度。 -/
theorem width_syntax_l (R L : set_l ℳ) (q w n : num_l ℳ) :
    Formula.satisfies ((((((Env.empty (M := ℳ)).pushFree L).pushFree R).pushFree w).pushFree q).pushFree n)
      width_m ↔ ∃ y, relation_l R (value_l q n) y ∧ relation_l L y (mul_l w n) := by
  simp only [width_m, Formula.satisfies, output_syntax_l, SecondOrderPairing.edge_l]
  rfl

/-- 同一原块的任意内部次数复制，存在宽度为块宽乘次数的实际输出。 -/
theorem width_exists_l (hℳ : Theory.Models ℳ theory_m) {R L : set_l ℳ}
    (hR : graph_semantics_l (graph_m copies_m) R)
    (hL : graph_semantics_l (graph_m length_m) L) {b w : num_l ℳ}
    (hb : relation_l L b w) (A l n : num_l ℳ) : ∃ y,
    relation_l R (value_l (value_l b (value_l A l)) n) y ∧ relation_l L y (mul_l w n) := by
  obtain ⟨C, hCf, hC⟩ := graph_total_l hℳ copy_m
  obtain ⟨P, hPf, hP⟩ := graph_total_l hℳ append_m
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  apply induct_l hℳ width_m width_language_m
    (((((Env.empty (M := ℳ)).pushFree L).pushFree R).pushFree w).pushFree (value_l b (value_l A l)))
    (fun n => ∃ y, relation_l R (value_l (value_l b (value_l A l)) n) y ∧ relation_l L y (mul_l w n))
    (width_syntax_l R L (value_l b (value_l A l)) w) ?_ ?_ n
  · refine ⟨zero_l ℳ, (copies_zero_l hℳ hR _ _).mpr rfl, ?_⟩
    rw [mul_zero_l hℳ]
    exact (length_rel_l hℳ hL hI _ _).mpr ((length_zero_l hℳ hI _).mpr rfl)
  · rintro k ⟨v, hv, hlv⟩
    obtain ⟨s, hs, _⟩ := hCf (value_l b (value_l A (value_l k l)))
    obtain ⟨y, hy, _⟩ := hPf (value_l v s)
    have hls := SecondOrderProgramCopyBlockShape.copy_width_l hℳ hC hL hs hb
    refine ⟨y, (copies_succ_l hℳ hR hC hP b A l k y).mpr ⟨v, s, hv, hs, hy⟩, ?_⟩
    rw [mul_succ_l hℳ]
    exact append_length_l hℳ hP hL hlv hls hy

/-- 真实图函数性使每个给定输出都具有精确的内部乘积宽度。 -/
theorem copies_width_l (hℳ : Theory.Models ℳ theory_m) {R L : set_l ℳ}
    (hR : graph_semantics_l (graph_m copies_m) R)
    (hL : graph_semantics_l (graph_m length_m) L) {b A l n w y : num_l ℳ}
    (hb : relation_l L b w) (hy : relation_l R (value_l (value_l b (value_l A l)) n) y) :
    relation_l L y (mul_l w n) := by
  obtain ⟨z, hz, hlz⟩ := width_exists_l hℳ hR hL hb A l n
  exact (function_value_unique_l (function_of_semantics_l hℳ copies_m hR) hz hy) ▸ hlz

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopiesShape
