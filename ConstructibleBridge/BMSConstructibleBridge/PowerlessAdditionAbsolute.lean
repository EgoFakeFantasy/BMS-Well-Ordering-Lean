import BMSConstructibleBridge.PowerlessAdditionIteration
import BMSConstructibleBridge.PowerlessAdditionSyntax
import BMSConstructibleBridge.PowerlessSourceGraphAbsolute

/-!
# 原无限迭代加法公式的传递子域绝对性

已有域内迭代图时，反向将自然数初值的值域选为实际 ω。
加法存在量词另行消费实际迭代图的成员性，不替换原加法公式。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessAdditionAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {A : carrier_l ℳ} {hA : ∃ x, member_l ℳ x A} (hAT : PowerlessNaturalOrder.transitive_l A)

include hℳ hAT

theorem iteration_l {ω e a F : type_l A} (hω : omega_l ω.val) (he : PowerlessNatural.zero_l e.val)
    (ha : member_l ℳ a.val ω.val) :
    PowerlessAddition.iteration_l (ℳ := structure_l A hA) ω e a F ↔
      PowerlessAddition.iteration_l ω.val e.val a.val F.val := by
  constructor
  · intro hF
    obtain ⟨B, hF, h₀, h₁⟩ := PowerlessAdditionIteration.equation_l.mp hF
    have hG := (PowerlessSourceGraphAbsolute.map_l hAT).mp hF
    apply PowerlessAdditionIteration.equation_l.mpr
    refine ⟨B.val, hG, (PowerlessSourceGraphAbsolute.value_l hAT).mp h₀, ?_⟩
    intro n m x y hn hm hx hy
    have hnA := hAT ω.val n ω.property hn
    have hmA := hAT ω.val m ω.property (PowerlessNatural.successor_mem_l hℳ hω hn hm)
    have hxA := hAT B.val x B.property (PowerlessFunction.value_mem_l hℳ hG hx).2
    have hyA := hAT B.val y B.property (PowerlessFunction.value_mem_l hℳ hG hy).2
    exact (PowerlessSourceNaturalAbsolute.successor_l hAT).mp
      (h₁ ⟨n, hnA⟩ ⟨m, hmA⟩ ⟨x, hxA⟩ ⟨y, hyA⟩ hn
        ((PowerlessSourceNaturalAbsolute.successor_l hAT).mpr hm)
        ((PowerlessSourceGraphAbsolute.value_l hAT).mpr hx) ((PowerlessSourceGraphAbsolute.value_l hAT).mpr hy))
  · intro hF
    have hG := PowerlessAdditionIteration.map_l hℳ hω he ha hF
    obtain ⟨_, _, h₀, h₁⟩ := PowerlessAdditionIteration.equation_l.mp hF
    apply PowerlessAdditionIteration.equation_l.mpr
    refine ⟨ω, (PowerlessSourceGraphAbsolute.map_l hAT).mpr hG,
      (PowerlessSourceGraphAbsolute.value_l hAT).mpr h₀, ?_⟩
    intro n m x y hn hm hx hy
    exact (PowerlessSourceNaturalAbsolute.successor_l hAT).mpr
      (h₁ n.val m.val x.val y.val hn ((PowerlessSourceNaturalAbsolute.successor_l hAT).mp hm)
        ((PowerlessSourceGraphAbsolute.value_l hAT).mp hx) ((PowerlessSourceGraphAbsolute.value_l hAT).mp hy))

theorem addition_l {ω e a b c : type_l A} (hω : omega_l ω.val) (he : PowerlessNatural.zero_l e.val)
    (ha : member_l ℳ a.val ω.val)
    (hF : ∀ F, PowerlessAddition.iteration_l ω.val e.val a.val F → member_l ℳ F A) :
    PowerlessAddition.addition_l (ℳ := structure_l A hA) ω e a b c ↔
      PowerlessAddition.addition_l ω.val e.val a.val b.val c.val := by
  constructor
  · rintro ⟨F, h₀, hc⟩
    exact ⟨F.val, (iteration_l hℳ hAT hω he ha).mp h₀, (PowerlessSourceGraphAbsolute.value_l hAT).mp hc⟩
  · rintro ⟨F, h₀, hc⟩
    exact ⟨⟨F, hF F h₀⟩, (iteration_l hℳ hAT hω he ha).mpr h₀, (PowerlessSourceGraphAbsolute.value_l hAT).mpr hc⟩

theorem source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l A hA) Γ Δ) (ω e a b c : Term ℒ Γ Δ .set)
    (hω : omega_l (ω.eval η).val) (he : PowerlessNatural.zero_l (e.eval η).val)
    (ha : member_l ℳ (a.eval η).val (ω.eval η).val)
    (hF : ∀ F, PowerlessAddition.iteration_l (ω.eval η).val (e.eval η).val (a.eval η).val F → member_l ℳ F A) :
    Formula.satisfies η (PowerlessAdditionSyntax.addition_m ω e a b c) ↔
      PowerlessAddition.addition_l (ω.eval η).val (e.eval η).val (a.eval η).val (b.eval η).val (c.eval η).val :=
  (PowerlessAdditionSyntax.addition_formula_l η ω e a b c).trans (addition_l hℳ hAT hω he ha hF)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessAdditionAbsolute
