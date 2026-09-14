import BMSConstructibleBridge.PowerlessLevyGeneration
import YesMetaZFC.Logic.FirstOrder.LevyHierarchy

/-!
# 原源 Lévy 极性与内部标签的对应

复用原 LevyPolarity；这里只给其内部 0/1 表示，不增加源语法种类。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourcePolarity

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def code_l (e t : carrier_l ℳ) : Formula.LevyPolarity → carrier_l ℳ
  | .sigma => e
  | .pi => t

theorem flip_l (p : Formula.LevyPolarity) : p.flip.flip = p := by
  cases p <;> rfl

theorem polarity_l (e t : carrier_l ℳ) (p : Formula.LevyPolarity) :
    PowerlessLevyEntry.polarity_l e t (code_l e t p) := by
  cases p
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem opposite_l (e t : carrier_l ℳ) (p : Formula.LevyPolarity) :
    PowerlessLevyEntry.opposite_l e t (code_l e t p.flip) (code_l e t p) := by
  cases p
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

theorem natural_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (p : Formula.LevyPolarity) :
    member_l ℳ (code_l e t₁ p) ω := by
  cases p
  · exact (PowerlessEvaluationTags.natural_l hℳ hω ht).1
  · exact (PowerlessEvaluationTags.natural_l hℳ hω ht).2.1

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourcePolarity
