import BMSConstructibleBridge.SecondOrderProgramRunClosedSet
import BMSConstructibleBridge.SecondOrderProgramExpansionRectangular

/-!
# 原内部生成历史保持矩形性

使用真实理解公式收集共同列高不超过固定初始高度的全部矩形数组码，原展开保持
此集合，故原run的每个内部轨迹都保留矩形性及该高度界。并不把初始高度与目标
闭句限制的当前裁剪高度等同，也不假定轨迹或数组码外部标准。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramRunRectangular

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramRectangular (rectangular_l rectangular_m rectangular_syntax_l)
open SecondOrderProgramRun (run_m)
open SecondOrderProgramExpansion (expand_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 自由槽[数组x,高度上界H,L,E]；内部存在实际宽度n与共同列高g<=H。 -/
def bounded_m : Formula signature_m [] [.num, .num, .set, .set] :=
  .existsE .num (.existsE .num (.conj
    (rectangular_m (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar .here) (.bvar (.there .here)) (.bvar .here))
    (.disj (.equal (.bvar .here) (.fvar (.there .here)))
      (PrimitiveFormulas.lt_m (.bvar .here) (.fvar (.there .here))))))

/-- 有界矩形性公式中的高度界仅是给定内部H，不是外部有限数。 -/
theorem bounded_syntax_l (L E : set_l ℳ) (H x : num_l ℳ) :
    Formula.satisfies (((((Env.empty (M := ℳ)).pushFree E).pushFree L).pushFree H).pushFree x) bounded_m ↔
      ∃ n g, rectangular_l L E x n g ∧ (g = H ∨ SecondOrderOrder.lt_l g H) := by
  simp only [bounded_m, Formula.satisfies, rectangular_syntax_l, SecondOrderOrder.formula_l]
  rfl

/-- 有界矩形数组码由实际理解收集为模型内部集合。 -/
theorem bounded_set_l (hℳ : Theory.Models ℳ theory_m) (L E : set_l ℳ) (H : num_l ℳ) :
    ∃ S : set_l ℳ, ∀ x, mem_l x S ↔
      ∃ n g, rectangular_l L E x n g ∧ (g = H ∨ SecondOrderOrder.lt_l g H) := by
  obtain ⟨S, hS⟩ := comprehension_l hℳ bounded_m (pure_language_m _ rfl)
    ((((Env.empty (M := ℳ)).pushFree E).pushFree L).pushFree H)
  exact ⟨S, fun x => (hS x).trans (bounded_syntax_l L E H x)⟩

/-- 任意内部轨迹的原run输出仍矩形，实际共同列长不超过初始共同列长。 -/
theorem run_rectangular_l (hℳ : Theory.Models ℳ theory_m) {R L E : set_l ℳ}
    (hR : graph_semantics_l (graph_m run_m) R)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {v n h t y : num_l ℳ}
    (hv : rectangular_l L E v n h) (hy : relation_l R (value_l t v) y) :
    letI := order_l hℳ
    ∃ m g, rectangular_l L E y m g ∧ g ≤ h := by
  letI := order_l hℳ
  obtain ⟨X, _, hX⟩ := graph_total_l hℳ expand_m
  obtain ⟨S, hS⟩ := bounded_set_l hℳ L E h
  have hclosed (v i w : num_l ℳ) (hv : mem_l v S) (hw : relation_l X (value_l v i) w) : mem_l w S := by
    obtain ⟨n', h', hvr, hh⟩ := (hS v).mp hv
    obtain ⟨m, g, hwr, hgh⟩ := SecondOrderProgramExpansionRectangular.expand_rectangular_l hℳ hX hL hE hvr hw
    exact (hS w).mpr ⟨m, g, hwr, le_trans hgh (show h' ≤ h from hh)⟩
  have hvs : mem_l v S := (hS v).mpr ⟨n, h, hv, Or.inl rfl⟩
  exact (hS y).mp (SecondOrderProgramRunClosedSet.run_mem_l hℳ hR hX hclosed hvs hy)

#print axioms bounded_m
#print axioms bounded_syntax_l
#print axioms bounded_set_l
#print axioms run_rectangular_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramRunRectangular
