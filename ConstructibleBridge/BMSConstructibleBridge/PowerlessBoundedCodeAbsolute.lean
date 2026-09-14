import BMSConstructibleBridge.PowerlessFormulaCodeAbsolute
import BMSConstructibleBridge.PowerlessBoundedCode

/-!
# 原有界量词数码的绝对性

四个原构造子之间的中间数码由其自然数 guard 取回。
不改变有界量词正文，也不假定小结构满足无幂集核心。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedCodeAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {B : carrier_l ℳ} {hB : ∃ x, member_l ℳ x B} (hBT : PowerlessNaturalOrder.transitive_l B)
  {ω e T : type_l B} (hω : omega_l ω.val) (he : PowerlessNatural.zero_l e.val)
  (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
  (hI : ∀ x, member_l ℳ x ω.val → ∀ F,
    PowerlessAddition.iteration_l ω.val e.val x F → member_l ℳ F B)

include hℳ hBT hω he hT hI

theorem code_l {t₂ t₃ i j b c : type_l B} :
    PowerlessBoundedCode.code_l (ℳ := structure_l B hB) ω e T t₂ t₃ i j b c ↔
      PowerlessBoundedCode.code_l ω.val e.val T.val t₂.val t₃.val i.val j.val b.val c.val := by
  constructor
  · rintro ⟨hij, d, p, q, hd, hp, hq, hc⟩
    exact ⟨fun h => hij (Subtype.ext h), d.val, p.val, q.val,
      (PowerlessFormulaCodeAbsolute.constructor_l hℳ hBT hω he hT hI).mp hd,
      (PowerlessFormulaCodeAbsolute.constructor_l hℳ hBT hω he hT hI).mp hp,
      (PowerlessFormulaCodeAbsolute.constructor_l hℳ hBT hω he hT hI).mp hq,
      (PowerlessFormulaCodeAbsolute.constructor_l hℳ hBT hω he hT hI).mp hc⟩
  · rintro ⟨hij, d, p, q, hd, hp, hq, hc⟩
    have hdB := hBT ω.val d ω.property hp.1
    have hpB := hBT ω.val p ω.property hq.1
    have hqB := hBT ω.val q ω.property hc.2.1
    exact ⟨fun h => hij (congrArg Subtype.val h), ⟨d, hdB⟩, ⟨p, hpB⟩, ⟨q, hqB⟩,
      (PowerlessFormulaCodeAbsolute.constructor_l hℳ hBT hω he hT hI).mpr hd,
      (PowerlessFormulaCodeAbsolute.constructor_l hℳ hBT hω he hT hI).mpr hp,
      (PowerlessFormulaCodeAbsolute.constructor_l hℳ hBT hω he hT hI).mpr hq,
      (PowerlessFormulaCodeAbsolute.constructor_l hℳ hBT hω he hT hI).mpr hc⟩

theorem source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l B hB) Γ Δ)
    (w z U t₂ t₃ i j b c : Term ℒ Γ Δ .set)
    (hw : w.eval η = ω) (hz : z.eval η = e) (hU : U.eval η = T) :
    Formula.satisfies η (PowerlessBoundedCode.code_m w z U t₂ t₃ i j b c) ↔
      PowerlessBoundedCode.code_l ω.val e.val T.val (t₂.eval η).val (t₃.eval η).val
        (i.eval η).val (j.eval η).val (b.eval η).val (c.eval η).val := by
  rw [PowerlessBoundedCode.code_formula_l, hw, hz, hU]
  exact code_l hℳ hBT hω he hT hI

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedCodeAbsolute
