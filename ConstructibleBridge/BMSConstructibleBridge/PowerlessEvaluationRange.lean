import BMSConstructibleBridge.PowerlessEvaluationRecursion
import BMSConstructibleBridge.PowerlessOrdinalHistory

/-!
# 内部自然数递归的求值范围保持

在有限前史闭包和实际求值步骤闭包下，对原纯公式作模型内部归纳。
F 可在域外；归纳覆盖全部内部自然数，而非宿主 Nat 的标准长度。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationRange

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem value_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ S F U : carrier_l ℳ} (hω : omega_l ω)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F)
    (hG : ∀ n, member_l ℳ n ω → ∀ H, map_l H n U → member_l ℳ H U)
    (hS : ∀ n H Y, member_l ℳ n ω → member_l ℳ H U →
      PowerlessEvaluationStep.step_l ω e T A t₁ t₂ t₃ S H n Y → member_l ℳ Y U) :
    ∀ n Y, ThirdOrderSemantics.value_l F n Y → member_l ℳ Y U := by
  obtain ⟨D, hF, hE⟩ := hF
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 2 :=
    { bound := Fin.cases F (fun _ => U), free := fun _ => ω }
  let φ : Formula ℒ [] [.set, .set, .set] := .forallE .set (.imp
    (SecondOrderObjectSyntax.member_m (.bvar .here) (.fvar .here))
    (.forallE .set (.imp
      (SecondOrderObjectSyntax.value_m (.fvar (.there .here)) (.bvar (.there .here)) (.bvar .here))
      (SecondOrderObjectSyntax.member_m (.bvar .here) (.fvar (.there (.there .here)))))))
  have h : ∀ n, φ.satisfies ((PowerlessComprehension.env_l η).pushFree n) ↔
      ∀ k, member_l ℳ k n → ∀ Y, ThirdOrderSemantics.value_l F k Y → member_l ℳ Y U := by
    intro n
    simp only [φ, Formula.satisfies, value_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval]
    rfl
  have h₀ := PowerlessNatural.induction_l hℳ φ η hω
    (fun z hz => (h z).mpr (fun k hk _ _ => (hz k hk).elim))
    (fun n m hn hm h₁ => (h m).mpr (by
      intro k hk Y hY
      rcases (hm k).mp hk with hk | hk
      · exact (h n).mp h₁ k hk Y hY
      · subst k
        obtain ⟨H, hH, hY⟩ := hE n Y hY
        have hH₀ := PowerlessOrdinalHistory.map_l hℳ (PowerlessOmegaOrdinal.ordinal_l hℳ hω) hF hn hH
        apply hS n H Y hn (hG n hn H (PowerlessFunction.range_l hℳ hH₀ ?_)) hY
        intro k Z hZ
        obtain ⟨hZ, hk⟩ := (PowerlessEvaluationHistory.value_l hℳ hH).mp hZ
        exact (h n).mp h₁ k hk Z hZ))
  intro n Y hY
  obtain ⟨m, hm⟩ := PowerlessNatural.successor_exists_l hℳ n
  have hn := (PowerlessFunction.value_mem_l hℳ hF hY).1
  exact (h m).mp (h₀ m (PowerlessNatural.successor_mem_l hℳ hω hn hm))
    n ((hm n).mpr (Or.inr rfl)) Y hY

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationRange
