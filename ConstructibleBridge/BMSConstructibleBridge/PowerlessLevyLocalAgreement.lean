import BMSConstructibleBridge.PowerlessQuantifierDirection
import BMSConstructibleBridge.PowerlessBoundedCode

/-!
# 实际求值方程的极性保持规则

先核验同一赋值图在两域求值系统中的成员性，再读同一码的实际方程。
NAND 用逆向子查询，有界规则用传递性，无界 Σ 存在只向上提升见证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLevyLocalAgreement

open Logic FirstOrder ThirdOrderSemantics PowerlessEvaluationDirection
open PowerlessEvaluationClause (query_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem assignments_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω A U S R f : carrier_l ℳ} (hAU : subset_l A U)
    (hS : ∀ f, member_l ℳ f S ↔ ∃ m, member_l ℳ m ω ∧ map_l f m U)
    (hR : ∀ f, member_l ℳ f R ↔ ∃ m, member_l ℳ m ω ∧ map_l f m A)
    (hf : ∃ m, member_l ℳ m ω ∧ map_l f m A) : member_l ℳ f S ∧ member_l ℳ f R := by
  obtain ⟨m, hm, hf⟩ := hf
  exact ⟨(hS f).mpr ⟨m, hm, PowerlessFunction.range_l hℳ hf
    (fun _ y hy => hAU y (PowerlessFunction.value_mem_l hℳ hf hy).2)⟩, (hR f).mpr ⟨m, hm, hf⟩⟩

variable (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T A U t₁ t₂ t₃ S R F G : carrier_l ℳ} (hω : omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
  (hAU : subset_l A U)
  (hS : ∀ f, member_l ℳ f S ↔ ∃ m, member_l ℳ m ω ∧ map_l f m U)
  (hR : ∀ f, member_l ℳ f R ↔ ∃ m, member_l ℳ m ω ∧ map_l f m A)
  (hF : PowerlessEvaluationRecursion.evaluation_l ω e T U t₁ t₂ t₃ S F)
  (hG : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ R G)

include hℳ hω ht hT hAU hS hR hF hG

theorem nand_l {a b c p q : carrier_l ℳ} (hp : PowerlessLevyEntry.opposite_l e t₁ p q)
    (hc : PowerlessFormulaConstructor.constructor_l ω e T t₂ a b c)
    (ha : polarity_l ω A F G e t₁ q a) (hb : polarity_l ω A F G e t₁ q b) :
    polarity_l ω A F G e t₁ p c := by
  exact PowerlessEvaluationDirection.nand_polarity_l (PowerlessEvaluationTags.distinct_l hℳ ht).1 hp
    (fun f hf => (PowerlessEvaluationEquations.nand_l hℳ hω ht hT hF hc f).trans
      (and_iff_right (assignments_l hℳ hAU hS hR hf).1))
    (fun f hf => (PowerlessEvaluationEquations.nand_l hℳ hω ht hT hG hc f).trans
      (and_iff_right (assignments_l hℳ hAU hS hR hf).2)) ha hb

theorem bounded_l {i j b c p : carrier_l ℳ} (hA : PowerlessNaturalOrder.transitive_l A)
    (hc : PowerlessBoundedCode.code_l ω e T t₂ t₃ i j b c) (hb : polarity_l ω A F G e t₁ p b) :
    polarity_l ω A F G e t₁ p c := by
  constructor
  · intro hp f hf h
    have h₀ := assignments_l hℳ hAU hS hR hf
    exact (PowerlessBoundedCode.equation_l hℳ hω ht hT hF hS hc f h₀.1).mpr
      (PowerlessQuantifierDirection.bounded_up_l hℳ hAU (hb.1 hp)
        ((PowerlessBoundedCode.equation_l hℳ hω ht hT hG hR hc f h₀.2).mp h))
  · intro hp f hf h
    have h₀ := assignments_l hℳ hAU hS hR hf
    exact (PowerlessBoundedCode.equation_l hℳ hω ht hT hG hR hc f h₀.2).mpr
      (PowerlessQuantifierDirection.bounded_down_l hℳ hA hf (hb.2 hp)
        ((PowerlessBoundedCode.equation_l hℳ hω ht hT hF hS hc f h₀.1).mp h))

theorem existential_l {i b c : carrier_l ℳ}
    (hc : PowerlessFormulaConstructor.constructor_l ω e T t₃ i b c) (hb : direction_l ω A G F b) :
    direction_l ω A G F c := by
  intro f hf h
  exact (PowerlessEvaluationEquations.exists_l hℳ hω ht hT hF hc f).mpr
    ⟨(assignments_l hℳ hAU hS hR hf).1, PowerlessQuantifierDirection.exists_l hℳ hAU hb
      ((PowerlessEvaluationEquations.exists_l hℳ hω ht hT hG hc f).mp h).2⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLevyLocalAgreement
