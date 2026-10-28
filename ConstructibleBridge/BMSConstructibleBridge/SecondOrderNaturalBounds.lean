import BMSConstructibleBridge.PowerlessBMSQuotientInduction
import BMSConstructibleBridge.PowerlessBMSQuotientRecursion
import BMSConstructibleBridge.PowerlessNaturalStep

/-! # 无 Collection 的内部自然数后继边界

对原有纯边界公式的图翻译作原 Z₂ 归纳。量化原商全部对象，
不是对宿主自然数或外部良基序型作归纳。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderNaturalBounds

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem induction_derives_m : Derives SecondOrderArithmetic.theory_m []
    (SecondOrderArithmetic.induction_m (GraphTranslation.form_m PowerlessNaturalStep.bound_m)) :=
  GraphTranslation.induction_m PowerlessNaturalStep.bound_m

theorem bound_l (K : source_coding_l hℳ) {n : type_l hℳ} (hn : mem_l hℳ n K.omega) :
    ∀ a b : type_l hℳ, mem_l hℳ a n →
      PowerlessNatural.successor_l (ℳ := SecondOrderQuotient.structure_l hℳ) a b →
        mem_l hℳ b n ∨ b = n := by
  have h := PowerlessBMSQuotientInduction.induction_l K PowerlessNaturalStep.bound_m
    (Env.empty (M := SecondOrderQuotient.structure_l hℳ)) ?_ ?_
  · obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨n, hn⟩
    have hEq : (numberCode_l K i).val = n := congrArg Subtype.val hi
    have h' := (PowerlessNaturalStep.bound_formula_l _).mp (h i)
    change ∀ a b : type_l hℳ, mem_l hℳ a (numberCode_l K i).val →
      PowerlessNatural.successor_l (ℳ := SecondOrderQuotient.structure_l hℳ) a b →
        mem_l hℳ b (numberCode_l K i).val ∨ b = (numberCode_l K i).val at h'
    rw [hEq] at h'
    exact h'
  · apply (PowerlessNaturalStep.bound_formula_l _).mpr
    intro a b ha _
    exact (PowerlessBMSQuotientSuccessor.zero_l K a ha).elim
  · intro i hi
    apply (PowerlessNaturalStep.bound_formula_l _).mpr
    intro a b ha hb
    have hSucc := PowerlessBMSQuotientSuccessor.successor_l K i
    rcases (hSucc a).mp ha with ha | ha
    · exact Or.inl ((hSucc b).mpr ((PowerlessNaturalStep.bound_formula_l _).mp hi a b ha hb))
    · subst a
      exact Or.inr (PowerlessBMSQuotientRecursion.successor_unique_l hb hSucc)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderNaturalBounds
