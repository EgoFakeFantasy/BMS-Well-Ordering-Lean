import BMSConstructibleBridge.SecondOrderProgramParentHeightBound
import BMSConstructibleBridge.SecondOrderProgramFallbackDescent
import BMSConstructibleBridge.SecondOrderDecodedCounterexample
import BMSConstructibleBridge.SecondOrderCompleteness

/-!
# 原固定当前高度目标的零高度实例

任意Z₂模型中，原矩阵的反例会给出全零数组上的内部严格展开链。全零坐标使实际
最大父行始终为none，这与已证无父链终止矛盾。随后只作原零数码替换，经同签名
强完备性取得普通Derives；没有更换生成数组目标，也没有假定数域外部标准。
本节仅完成n=0，不是逐任意固定n的最终证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderZeroHeight

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderProgramSemantics SecondOrderProgramTotality
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

/-- 原矩阵在任意模型的零高度环境中为真，量化同一个任意内部反例实数。 -/
theorem matrix_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (η : Env ℳ [.set] [.num])
    (hzero : η.freeVal .here = zero_l ℳ) :
    Formula.satisfies η SecondOrderConcreteFormula.matrix_m := by
  classical
  by_contra hbad
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ SecondOrderProgramGeneratedDecode.decode_m
  obtain ⟨E, _, hE⟩ := graph_total_l hℳ SecondOrderProgramExpansion.expand_m
  obtain ⟨K, _, hK⟩ := graph_total_l hℳ SecondOrderProgramListLookup.lookup_m
  obtain ⟨M, _, hM⟩ := graph_total_l hℳ SecondOrderProgramMaximalParentRow.maximal_m
  obtain ⟨L, _, hL⟩ := graph_total_l hℳ SecondOrderProgramLength.length_m
  obtain ⟨Y, hY, _, hbound, hstep⟩ :=
    SecondOrderDecodedCounterexample.arrays_l hℳ hD hE hK η hbad
  apply SecondOrderProgramFallbackDescent.no_chain_l hℳ hE hM hL hY ?_ hstep
  intro i x hx
  have hz := hbound i x hx
  rw [hzero] at hz
  exact SecondOrderProgramParentHeightBound.maximal_zero_l hℳ hM hK hz

/-- 原同一闭句closed_m 0对所有Z₂模型成立，而非只对标准模型成立。 -/
theorem models_l (ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m)
    (hℳ : Theory.Models ℳ theory_m) : (SecondOrderConcreteFormula.closed_m 0).TrueIn ℳ := by
  change Formula.satisfies (Env.empty (M := ℳ))
    (PureSecondOrder.closed_m SecondOrderConcreteFormula.matrix_m 0)
  rw [PureSecondOrder.closed_m, Formula.satisfies_instantiateFreeTop]
  intro X
  exact matrix_l hℳ _ rfl

/-- Z₂的普通Hilbert推导：原固定当前高度目标在零高度处的实际闭句。 -/
theorem derives_m : Derives theory_m [] (SecondOrderConcreteFormula.closed_m 0) :=
  SecondOrderCompleteness.derives_m models_l

#print axioms matrix_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderZeroHeight
