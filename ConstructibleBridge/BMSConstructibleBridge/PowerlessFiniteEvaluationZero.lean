import BMSConstructibleBridge.PowerlessFiniteEvaluationRelation

/-! # 实际有限求值图在零码处恒假

四个构造子都输出非零码。直接读取有限历史中的零列即可排除零码真值，
无需预设整张图的递归方程或源理论模型；供源语言 falsum 分支使用。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteEvaluationZero

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

theorem clause_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {ω e T A t₁ t₂ t₃ H z f : carrier_l 𝒩} (hz : PowerlessNatural.zero_l (ℳ := 𝒩) z) :
    ¬PowerlessEvaluationClause.clause_l ω e T A t₁ t₂ t₃ H z f := by
  rintro (⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩) <;>
    exact PowerlessFormulaConstructor.nonzero_l hz h rfl

theorem relation_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {C ω e N T A S t₁ t₂ t₃ Q G : type_l hℳ}
    (hω : omega_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω)
    (he : PowerlessNatural.zero_l (ℳ := SecondOrderQuotient.structure_l hℳ) e)
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω ω N)
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T ω ω)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω A S)
    (hG : PowerlessFiniteEvaluationRelation.spec_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      C ω e N T A S t₁ t₂ t₃ Q G) (f : type_l hℳ) :
    ¬value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G e f := by
  intro hf
  obtain ⟨_, _, m, _, F, _, hem, hF, Y, hY, hfY⟩ := (hG e f).mp hf
  have hYC := (SecondOrderFunctionProperties.value_mem_l hℳ hF.1 hY).2
  obtain ⟨H, _, _, hStep⟩ := hF.2 e hem Y hYC hY
  have hStep' := (PowerlessEvaluationStepBounded.step_iff_l (hℳ := hℳ) hω he hN hT hS).mp hStep
  exact clause_l he ((hStep' f).mp hfY).2

def formula_m {Γ Δ : SortContext ℒ} (e G : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .neg <| SecondOrderObjectSyntax.value_m
    (G.weakenBound SetTheory.SetSort.set) (e.weakenBound SetTheory.SetSort.set) (.bvar .here)

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (e G : Term ℒ Γ Δ .set) :
    (formula_m e G).satisfies η ↔ ∀ f, ¬value_l (ℳ := 𝒩) (G.eval η) (e.eval η) f := by
  simp only [formula_m, Formula.satisfies, value_formula_l, Term.eval_weakenBound, Term.eval]
  rfl

#print axioms relation_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteEvaluationZero
