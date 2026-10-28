import BMSConstructibleBridge.SecondOrderFunctions

/-!
# 内部全函数实数的复合

用原二元关系理解的实际纯公式构造复合图。输入、输出及中间值均在模型内部，
不把任意外部函数族收集成实数；供下降轨迹逐点运行同一解码程序使用。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFunctionComposition

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 自由槽为输入、输出、第一图、第二图；唯一数量词绑定中间值。 -/
def composition_m : Formula signature_m [] [.num, .num, .set, .set] :=
  .existsE .num (.conj
    (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.fvar .here) (.bvar .here))
    (GraphSyntax.edge_m (.fvar (.there (.there (.there .here))))
      (.bvar .here) (.fvar (.there .here))))

/-- 复合模板只含数量词及原两个关系实数参数。 -/
theorem composition_language_m : language_m composition_m = true := pure_language_m _ rfl

/-- 模板严格按照先X后D的顺序解释。 -/
theorem composition_syntax_l (X D : set_l ℳ) (i u : num_l ℳ) :
    Formula.satisfies (((((Env.empty (M := ℳ)).pushFree D).pushFree X).pushFree u).pushFree i)
      composition_m ↔ ∃ a, relation_l X i a ∧ relation_l D a u := by
  simp only [composition_m, Formula.satisfies, SecondOrderPairing.edge_l]
  rfl

/-- 原模型中存在这张复合实数，并给出所有内部坐标上的精确规格。 -/
theorem exists_l (hℳ : Theory.Models ℳ theory_m) (X D : set_l ℳ) :
    ∃ Y : set_l ℳ, ∀ i u, relation_l Y i u ↔ ∃ a, relation_l X i a ∧ relation_l D a u := by
  obtain ⟨Y, hY⟩ := SecondOrderRelations.comprehension_l hℳ composition_m composition_language_m
    (((Env.empty (M := ℳ)).pushFree D).pushFree X)
  exact ⟨Y, fun i u => (hY i u).trans (composition_syntax_l X D i u)⟩

/-- 两个实际内部全函数的复合仍是全函数；不要求配对域外的条件。 -/
theorem function_l {X D Y : set_l ℳ}
    (hX : SecondOrderFunctions.function_l X) (hD : SecondOrderFunctions.function_l D)
    (hY : ∀ i u, relation_l Y i u ↔ ∃ a, relation_l X i a ∧ relation_l D a u) :
    SecondOrderFunctions.function_l Y := by
  intro i
  obtain ⟨a, ha, hua⟩ := hX i
  obtain ⟨u, hu, huu⟩ := hD a
  refine ⟨u, (hY i u).mpr ⟨a, ha, hu⟩, ?_⟩
  intro v hv
  obtain ⟨b, hb, hv⟩ := (hY i v).mp hv
  have hba : b = a := hua b hb
  exact huu v (hba ▸ hv)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFunctionComposition
