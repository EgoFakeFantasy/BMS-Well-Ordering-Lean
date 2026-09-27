import BMSConstructibleBridge.SecondOrderMinimum

/-!
# 内部数值函数的值域最小元

用实际存在公式在同一模型中收集值域，再应用内部最小元原理。结论排除由模型内
实数编码的逐步严格下降函数，不宣称非标准数域在宿主意义下良基。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFunctionMinimum

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 自由槽[输出,F]，唯一数量词绑定输入，保留同一个函数实数。 -/
def range_m : Formula signature_m [] [.num, .set] :=
  .existsE .num (GraphSyntax.edge_m (.fvar (.there .here)) (.bvar .here) (.fvar .here))

/-- 值域公式的语义是存在内部输入，不是存在宿主函数的外部下标。 -/
theorem range_syntax_l (F : set_l ℳ) (n : num_l ℳ) :
    Formula.satisfies (((Env.empty (M := ℳ)).pushFree F).pushFree n) range_m ↔
      ∃ i, relation_l F i n := by
  simp only [range_m, Formula.satisfies, SecondOrderPairing.edge_l]
  rfl

/-- 任意内部全函数的值域有一个实际达到的最小值。 -/
theorem minimum_l (hℳ : Theory.Models ℳ theory_m) {F : set_l ℳ} (hF : function_l F) :
    ∃ i n, relation_l F i n ∧ ∀ j m, relation_l F j m → ¬SecondOrderOrder.lt_l m n := by
  obtain ⟨X, hX⟩ := comprehension_l hℳ range_m (pure_language_m _ rfl)
    ((Env.empty (M := ℳ)).pushFree F)
  have hr (n : num_l ℳ) : mem_l n X ↔ ∃ i, relation_l F i n :=
    (hX n).trans (range_syntax_l F n)
  obtain ⟨a, ha, _⟩ := hF (zero_l ℳ)
  obtain ⟨n, hn, hmin⟩ := SecondOrderMinimum.exists_l hℳ X ⟨a, (hr a).mpr ⟨_, ha⟩⟩
  obtain ⟨i, hi⟩ := (hr n).mp hn
  exact ⟨i, n, hi, fun j m hm hlt => hmin m hlt ((hr m).mpr ⟨j, hm⟩)⟩

/-- 同一内部全函数不能在每个后继位置严格下降。 -/
theorem not_descending_l (hℳ : Theory.Models ℳ theory_m) {F : set_l ℳ}
    (hF : function_l F)
    (hstep : ∀ i a b, relation_l F i a → relation_l F (succ_l i) b →
      SecondOrderOrder.lt_l b a) : False := by
  obtain ⟨i, n, hi, hmin⟩ := minimum_l hℳ hF
  obtain ⟨b, hb, _⟩ := hF (succ_l i)
  exact hmin (succ_l i) b hb (hstep i n b hi hb)

#print axioms range_m
#print axioms range_syntax_l
#print axioms minimum_l
#print axioms not_descending_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFunctionMinimum
