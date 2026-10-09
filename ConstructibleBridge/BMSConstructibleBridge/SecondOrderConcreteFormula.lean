import BMSConstructibleBridge.SecondOrderProgramGeneratedHeight
import BMSConstructibleBridge.SecondOrderProgramGeneratedCheck

/-!
# 原固定当前高度目标的具体程序矩阵

高度与一步检查器现在都是显式七构造程序，不再从原始递归存在证书中选择未知代码。
直接实例化原compiled_matrix_m与原closed_m，得到同一矩阵及全部外部高度的数码闭句。
本模块给出标准语义等价和任意 Z₂ 模型图总性；固定外部高度 H 的最终对象推导
已在 `SecondOrderHereditaryBMSWellOrder.derives_m H` 完成。该出口排除当前高度始终
≤ H 的无限严格一步展开下降链，不限制种子或历史高度，也不打包线性可比性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderConcreteFormula

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramGeneratedHeight (height_m height_eval_l)
open SecondOrderProgramGeneratedCheck (check_m check_eval_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

/-- 原目标模板的具体实例；两张图直接来自可审计的实际程序。 -/
def matrix_m : Formula signature_m [.set] [.num] :=
  FixedHeightPureFormula.compiled_matrix_m height_m check_m

/-- 具体矩阵仍使用原纯二阶算术语言。 -/
theorem matrix_pure_m : pure_m matrix_m = true :=
  FixedHeightPureFormula.compiled_matrix_pure height_m check_m

/-- 具体矩阵对全部外部高度具有原当前高度目标的标准语义。 -/
theorem matrix_sound_l (n : Nat) :
    Formula.satisfies (PureSecondOrder.environment_l n) (.forallE .set matrix_m) ↔
      FixedHeightSecondOrder.sentence_l n := by
  apply FixedHeightPureFormula.compiled_matrix_sound
  · funext x
    exact height_eval_l x
  · funext x
    exact check_eval_l x

/-- 所有高度实例只作原数码替换，不重新选择程序或公式。 -/
def closed_m (n : Nat) : Sentence signature_m := PureSecondOrder.closed_m matrix_m n

/-- 具体闭句保留一个最外层集合全称量词与纯算术矩阵。 -/
theorem closed_pure_m (n : Nat) : ∃ (φ : Formula signature_m [.set] []),
    closed_m n = .forallE .set φ ∧ pure_m φ = true :=
  PureSecondOrder.closed_pure_m matrix_m matrix_pure_m n

/-- 同一具体闭句的标准真值正好是原固定当前高度句。 -/
theorem closed_sound_l (n : Nat) :
    Formula.satisfies (Env.empty (M := structure_l)) (closed_m n) ↔
      FixedHeightSecondOrder.sentence_l n :=
  (PureSecondOrder.closed_l matrix_m n).trans (matrix_sound_l n)

/-- 任意原Z₂模型中存在这两个固定程序的实际总图，而非另选标准等价图。
这只是算法图的存在与唯一值，不是closed_m n的模型真值。 -/
theorem graphs_total_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) :
    ∃ H E : set_l ℳ, function_l H ∧ graph_semantics_l (graph_m height_m) H ∧
      function_l E ∧ graph_semantics_l (graph_m check_m) E := by
  obtain ⟨H, hHf, hH⟩ := graph_total_l hℳ height_m
  obtain ⟨E, hEf, hE⟩ := graph_total_l hℳ check_m
  exact ⟨H, E, hHf, hH, hEf, hE⟩

#print axioms matrix_m
#print axioms matrix_pure_m
#print axioms matrix_sound_l
#print axioms closed_m
#print axioms closed_pure_m
#print axioms closed_sound_l
#print axioms graphs_total_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderConcreteFormula
