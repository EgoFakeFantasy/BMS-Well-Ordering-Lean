import BMSConstructibleBridge.SecondOrderProgramCopyRectangular
import BMSConstructibleBridge.SecondOrderProgramRectangularSelection
import BMSConstructibleBridge.SecondOrderProgramCopies

/-!
# 任意内部次数的原多副本矩形性

归纳正文绑定同一实际copies输出与完整矩形性公式，固定原块而不是累计块。
后继把一份同高副本接到已有累计数组后；次数可以非标准。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopiesRectangular

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions
open SecondOrderProgramSemantics SecondOrderProgramTotality SecondOrderProgramArithmetic
open SecondOrderProgramRectangular
open SecondOrderProgramCopies (copies_m copies_zero_l copies_succ_l)
open SecondOrderProgramCopyBlock (copy_m)
open SecondOrderProgramListAppend (append_m)
open SecondOrderProgramLength (length_m length_rel_l)
open SecondOrderProgramListIteration (iterate_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramListShift (output_m output_syntax_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 自由槽[次数n,固定参数q,块宽w,共同高度h,R,L,E]；绑定实际输出y。 -/
def stage_m : Formula signature_m [] [.num, .num, .num, .num, .set, .set, .set] :=
  .existsE .num (.conj
    (output_m (.fvar (.there (.there (.there (.there .here))))) (.fvar (.there .here))
      (.fvar .here) (.bvar .here))
    (rectangular_m (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here))))))) (.bvar .here)
      (Term.app (σ := signature_m) .mul (.cons (.fvar (.there (.there .here))) (.cons (.fvar .here) .nil)))
      (.fvar (.there (.there (.there .here))))))

/-- 同高累计数组不变量是原纯语言公式。 -/
theorem stage_language_m : language_m stage_m = true := pure_language_m _ rfl

/-- 语法精确保留固定参数、真实累计输出以及乘积宽度。 -/
theorem stage_syntax_l (R L E : set_l ℳ) (q w h n : num_l ℳ) :
    Formula.satisfies ((((((((Env.empty (M := ℳ)).pushFree E).pushFree L).pushFree R).pushFree h).pushFree w).pushFree q).pushFree n)
      stage_m ↔ ∃ y, relation_l R (value_l q n) y ∧ rectangular_l L E y (mul_l w n) h := by
  simp only [stage_m, Formula.satisfies, output_syntax_l, rectangular_syntax_l]
  rfl

/-- 每个内部复制次数都有同高的实际累计输出，宽度为固定原块宽乘次数。 -/
theorem rectangular_exists_l (hℳ : Theory.Models ℳ theory_m) {R L E : set_l ℳ}
    (hR : graph_semantics_l (graph_m copies_m) R)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {b w h : num_l ℳ}
    (hb : rectangular_l L E b w h) (A l n : num_l ℳ) : ∃ y,
    relation_l R (value_l (value_l b (value_l A l)) n) y ∧ rectangular_l L E y (mul_l w n) h := by
  letI := order_l hℳ
  obtain ⟨C, hCf, hC⟩ := graph_total_l hℳ copy_m
  obtain ⟨P, hPf, hP⟩ := graph_total_l hℳ append_m
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  apply induct_l hℳ stage_m stage_language_m
    (((((((Env.empty (M := ℳ)).pushFree E).pushFree L).pushFree R).pushFree h).pushFree w).pushFree (value_l b (value_l A l)))
    (fun n => ∃ y, relation_l R (value_l (value_l b (value_l A l)) n) y ∧ rectangular_l L E y (mul_l w n) h)
    (stage_syntax_l R L E (value_l b (value_l A l)) w h) ?_ ?_ n
  · refine ⟨zero_l ℳ, (copies_zero_l hℳ hR _ _).mpr rfl, ?_⟩
    rw [mul_zero_l hℳ]
    refine ⟨(length_rel_l hℳ hL hI _ _).mpr
      ((SecondOrderProgramListLength.length_zero_l hℳ hI _).mpr rfl), ?_⟩
    intro j hj
    exact False.elim ((not_lt_of_ge (zero_le_l hℳ j)) hj)
  · rintro k ⟨v, hv, hvr⟩
    obtain ⟨s, hs, _⟩ := hCf (value_l b (value_l A (value_l k l)))
    obtain ⟨y, hy, _⟩ := hPf (value_l v s)
    have hsr := SecondOrderProgramCopyRectangular.copy_rectangular_l hℳ hC hL hE hb hs
    refine ⟨y, (copies_succ_l hℳ hR hC hP b A l k y).mpr ⟨v, s, hv, hs, hy⟩, ?_⟩
    rw [mul_succ_l hℳ]
    exact SecondOrderProgramRectangularSelection.append_rectangular_l hℳ hP hL hE hvr hsr hy

/-- 原copies图的每个给定输出都满足该矩形性，不需另选一个方便的输出。 -/
theorem copies_rectangular_l (hℳ : Theory.Models ℳ theory_m) {R L E : set_l ℳ}
    (hR : graph_semantics_l (graph_m copies_m) R)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {b w h A l n y : num_l ℳ}
    (hb : rectangular_l L E b w h)
    (hy : relation_l R (value_l (value_l b (value_l A l)) n) y) : rectangular_l L E y (mul_l w n) h := by
  obtain ⟨z, hz, hzr⟩ := rectangular_exists_l hℳ hR hL hE hb A l n
  exact (function_value_unique_l (function_of_semantics_l hℳ copies_m hR) hz hy) ▸ hzr

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopiesRectangular
