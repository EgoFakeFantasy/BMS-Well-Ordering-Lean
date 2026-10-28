import BMSConstructibleBridge.SecondOrderProgramCopyZero
import BMSConstructibleBridge.SecondOrderProgramCopiesShape

/-!
# 任意内部正次数的复制拼接保留原首副本

零号副本就是原块；之后的每个副本只追加在右侧。归纳正文是实际原图输出的
前缀读值公式，复制次数可为非标准内部数，不使用外部自然数归纳。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopiesFirst

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing
open SecondOrderProgramSemantics SecondOrderProgramTotality SecondOrderProgramArithmetic
open SecondOrderProgramCopies (copies_m copies_zero_l copies_succ_l)
open SecondOrderProgramCopyBlock (copy_m)
open SecondOrderProgramListAppend (append_m append_left_l append_right_l)
open SecondOrderProgramLength (length_m length_rel_l)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramListIteration (iterate_m)
open SecondOrderProgramListLength (length_zero_l)
open SecondOrderProgramListShift (output_m output_syntax_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 自由槽[k,q,b,w,R,E]：原R在succ k次的每个输出保留b的前w项。 -/
def first_m : Formula signature_m [] [.num, .num, .num, .num, .set, .set] :=
  .forallE .num (.imp
    (output_m (.fvar (.there (.there (.there (.there .here))))) (.fvar (.there .here))
      (Term.app (σ := signature_m) .succ (.cons (.fvar .here) .nil)) (.bvar .here))
    (SecondOrderProgramListExtensionality.entries_m
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there .here))) (.bvar .here) (.fvar (.there (.there (.there .here))))))

/-- 首副本保持的归纳正文属于原纯语言。 -/
theorem first_language_m : language_m first_m = true := pure_language_m _ rfl

/-- 实际公式覆盖原图的每个内部输出和前缀内每个源码值。 -/
theorem first_syntax_l (R E : set_l ℳ) (q b w k : num_l ℳ) :
    Formula.satisfies
      (((((((Env.empty (M := ℳ)).pushFree E).pushFree R).pushFree w).pushFree b).pushFree q).pushFree k)
      first_m ↔ ∀ y, relation_l R (value_l q (succ_l k)) y →
        SecondOrderProgramListExtensionality.entries_l E b y w := by
  simp only [first_m, Formula.satisfies, output_syntax_l,
    SecondOrderProgramListExtensionality.entries_syntax_l]
  rfl

/-- 真实copies在任意内部正次数上保留原块每个有效位置的同一列码。 -/
theorem entries_l (hℳ : Theory.Models ℳ theory_m) {R L E : set_l ℳ}
    (hR : graph_semantics_l (graph_m copies_m) R)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {b w : num_l ℳ}
    (hb : relation_l L b w) (A l k : num_l ℳ) : ∀ y,
    relation_l R (value_l (value_l b (value_l A l)) (succ_l k)) y →
      SecondOrderProgramListExtensionality.entries_l E b y w := by
  letI := order_l hℳ
  obtain ⟨C, _, hC⟩ := graph_total_l hℳ copy_m
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ append_m
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  have h00 : relation_l L (zero_l ℳ) (zero_l ℳ) :=
    (length_rel_l hℳ hL hI _ _).mpr ((length_zero_l hℳ hI _).mpr rfl)
  apply induct_l hℳ first_m first_language_m
    ((((((Env.empty (M := ℳ)).pushFree E).pushFree R).pushFree w).pushFree b).pushFree
      (value_l b (value_l A l)))
    (fun k => ∀ y, relation_l R (value_l (value_l b (value_l A l)) (succ_l k)) y →
      SecondOrderProgramListExtensionality.entries_l E b y w)
    (first_syntax_l R E (value_l b (value_l A l)) b w) ?_ ?_ k
  · intro y hy j hj a ha
    obtain ⟨v, s, hv, hs, hp⟩ := (copies_succ_l hℳ hR hC hP b A l (zero_l ℳ) y).mp hy
    have hv0 := (copies_zero_l hℳ hR _ _).mp hv
    have hsb := (SecondOrderProgramCopyZero.copy_zero_l hℳ hC b A l s).mp hs
    rw [← hv0, ← hsb] at hp
    have he := (append_right_l hℳ hP hL hE h00 hb hp hj a).mpr ha
    simpa only [SecondOrderNumbers.zero_add_l hℳ] using he
  · intro k ih y hy j hj a ha
    obtain ⟨v, s, hv, hs, hp⟩ := (copies_succ_l hℳ hR hC hP b A l (succ_l k) y).mp hy
    have hvw := SecondOrderProgramCopiesShape.copies_width_l hℳ hR hL hb hv
    have hsw := SecondOrderProgramCopyBlockShape.copy_width_l hℳ hC hL hs hb
    have hw : w ≤ mul_l w (succ_l k) := (le_iff_l hℳ _ _).mpr
      ⟨mul_l w k, by
        change add_l w (mul_l w k) = mul_l w (succ_l k)
        rw [mul_succ_l hℳ, SecondOrderNumbers.add_comm_l hℳ]⟩
    exact (append_left_l hℳ hP hL hE hvw hsw hp
      (show SecondOrderOrder.lt_l j (mul_l w (succ_l k)) from lt_of_lt_of_le hj hw) a).mpr
      (ih v hv j hj a ha)

/-- 首副本范围内，原多副本输出与原块的读取图逐值双向等价。 -/
theorem column_l (hℳ : Theory.Models ℳ theory_m) {R L E : set_l ℳ}
    (hR : graph_semantics_l (graph_m copies_m) R)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {b w A l k y j : num_l ℳ}
    (hb : relation_l L b w)
    (hy : relation_l R (value_l (value_l b (value_l A l)) (succ_l k)) y)
    (hj : SecondOrderOrder.lt_l j w) (a : num_l ℳ) :
    relation_l E (value_l y j) a ↔ relation_l E (value_l b j) a := by
  have hEf := function_of_semantics_l hℳ lookup_m hE
  obtain ⟨s, hs, _⟩ := hEf (value_l b j)
  have hys := entries_l hℳ hR hL hE hb A l k y hy j hj s hs
  constructor
  · intro hya
    rw [← function_value_unique_l hEf hys hya]
    exact hs
  · exact entries_l hℳ hR hL hE hb A l k y hy j hj a

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopiesFirst
