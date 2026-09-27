import BMSConstructibleBridge.PowerlessFunctionIteration

/-! # 实际自映射的内部迭代唯一性 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFunctionIteration

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

/-- 比较同一实际自映射的两张内部轨迹，不对模型自然数作宿主归纳。 -/
theorem unique_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e A H a f g : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hH : map_l H A A) (hf : iteration_l ω e A H a f) (hg : iteration_l ω e A H a g) :
    f = g := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 1 :=
    { bound := fun _ => H, free := fun _ => ω }
  let φ : Formula ℒ [] [.set, .set, .set] :=
    SecondOrderObjectSyntax.value_m (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)
  have h : ∀ x y, φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) ↔
      value_l H x y := fun x y => value_formula_l _ _ _ _
  exact PowerlessOmegaRecursion.unique_l hℳ φ η
    (fun x y z hy hz => PowerlessFunction.value_unique_l hℳ hH ((h x y).mp hy) ((h x z).mp hz))
    hω he ⟨A, hf.1, hf.2.1, fun n m x y hn hm hx hy =>
      (h x y).mpr (hf.2.2 n m x y hn hm hx hy)⟩
    ⟨A, hg.1, hg.2.1, fun n m x y hn hm hx hy =>
      (h x y).mpr (hg.2.2 n m x y hn hm hx hy)⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFunctionIteration
