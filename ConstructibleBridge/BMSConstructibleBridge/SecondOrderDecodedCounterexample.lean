import BMSConstructibleBridge.SecondOrderConcreteSemantics
import BMSConstructibleBridge.SecondOrderFunctionComposition

/-!
# 从原公式反例构造实际内部数组下降实数

对反例轨迹码实数X与同一解码图D做内部关系复合，获得数组码实数Y。Y的每项
当前高度都满足原界，相邻项由同一实际展开图严格相连。指标只保留逐步存在，
没有另作依赖选择或收集历史；本模块仍不证明这种内部数组下降实数不可能存在。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDecodedCounterexample

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramArithmetic SecondOrderProgramTotality
open SecondOrderProgramGeneratedDecode (decode_m)
open SecondOrderProgramGeneratedHeight (height_m height_rel_l)
open SecondOrderProgramGeneratedCheck (check_m check_one_l)
open SecondOrderProgramExpansion (expand_m)
open SecondOrderProgramTrimHeight (trim_m)
open SecondOrderProgramZeroRows (zero_rows_l trim_bound_iff_zero_rows_l)
open SecondOrderProgramListLookup (lookup_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原矩阵反例产生模型内的数组码全函数实数及同一程序的严格展开下降。
保留原反例到数组的逐点来源，后续生成性证明可继续消费实际解码图。 -/
theorem arrays_l (hℳ : Theory.Models ℳ theory_m) {D E K : set_l ℳ}
    (hD : graph_semantics_l (graph_m decode_m) D)
    (hE : graph_semantics_l (graph_m expand_m) E)
    (hK : graph_semantics_l (graph_m lookup_m) K) (η : Env ℳ [.set] [.num])
    (hbad : ¬Formula.satisfies η SecondOrderConcreteFormula.matrix_m) :
    ∃ Y : set_l ℳ, function_l Y ∧
      (∀ i u, relation_l Y i u ↔ ∃ a, relation_l (η.boundVal .here) i a ∧ relation_l D a u) ∧
      (∀ i u, relation_l Y i u → zero_rows_l K u (η.freeVal .here)) ∧
      ∀ i u v, relation_l Y i u → relation_l Y (succ_l i) v →
        ∃ k, relation_l E (value_l u k) v ∧ v ≠ u := by
  letI := order_l hℳ
  obtain ⟨H, _, hH⟩ := graph_total_l hℳ height_m
  obtain ⟨C, _, hC⟩ := graph_total_l hℳ check_m
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ trim_m
  obtain ⟨hX, hbound, hstep⟩ := (SecondOrderConcreteSemantics.counterexample_l hℳ hH hC η).mp hbad
  obtain ⟨Y, hY⟩ := SecondOrderFunctionComposition.exists_l hℳ (η.boundVal .here) D
  have hDf := function_of_semantics_l hℳ decode_m hD
  refine ⟨Y, SecondOrderFunctionComposition.function_l hX hDf hY, hY, ?_, ?_⟩
  · intro i u hu
    obtain ⟨a, ha, hdu⟩ := (hY i u).mp hu
    obtain ⟨h, hh, hle⟩ := hbound i a ha
    obtain ⟨w, hdw, hth⟩ := (height_rel_l hℳ hH hD hT a h).mp hh
    have hwu : w = u := function_value_unique_l hDf hdw hdu
    exact (trim_bound_iff_zero_rows_l hℳ hT hK (hwu ▸ hth) (η.freeVal .here)).mp hle
  · intro i u v hu hv
    obtain ⟨a, ha, hdu⟩ := (hY i u).mp hu
    obtain ⟨b, hb, hdv⟩ := (hY (succ_l i) v).mp hv
    obtain ⟨k, hk⟩ := hstep i a b ha hb
    obtain ⟨w, hew, _⟩ := function_of_semantics_l hℳ expand_m hE (value_l u k)
    obtain ⟨hvw, hne⟩ := (check_one_l hℳ hC hD hE b a k v u w hdv hdu hew).mp hk
    exact ⟨k, hvw ▸ hew, hne⟩

#print axioms arrays_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDecodedCounterexample
