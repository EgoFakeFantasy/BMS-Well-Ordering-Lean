import BMSConstructibleBridge.PowerlessAdditionFinite

/-! # 有限加法计算的原纯语言公式 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessAdditionFiniteSyntax

open Logic FirstOrder ThirdOrderSemantics PowerlessAdditionFinite

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def trace_m {Γ Δ : SortContext ℒ} (ω e a n g : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) :=
    let t₁ := t.weakenBound SetTheory.SetSort.set
    let t₂ := t₁.weakenBound SetTheory.SetSort.set
    let t₃ := t₂.weakenBound SetTheory.SetSort.set
    let t₄ := t₃.weakenBound SetTheory.SetSort.set
    t₄.weakenBound SetTheory.SetSort.set
  .existsE .set (.conj
    (PowerlessNaturalStep.successor_m (n.weakenBound SetTheory.SetSort.set) (.bvar .here))
    (.conj (SecondOrderObjectSyntax.map_m (g.weakenBound SetTheory.SetSort.set)
      (.bvar .here) (ω.weakenBound SetTheory.SetSort.set))
      (.conj (SecondOrderObjectSyntax.value_m (g.weakenBound SetTheory.SetSort.set)
        (e.weakenBound SetTheory.SetSort.set) (a.weakenBound SetTheory.SetSort.set))
        (.forallE .set (.forallE .set (.forallE .set (.forallE .set
          (.imp (SecondOrderObjectSyntax.member_m (.bvar (.there (.there (.there .here)))) (w n))
            (.imp (PowerlessNaturalStep.successor_m (.bvar (.there (.there (.there .here))))
              (.bvar (.there (.there .here))))
              (.imp (SecondOrderObjectSyntax.value_m (w g) (.bvar (.there (.there (.there .here))))
                (.bvar (.there .here)))
                (.imp (SecondOrderObjectSyntax.value_m (w g) (.bvar (.there (.there .here))) (.bvar .here))
                  (PowerlessNaturalStep.successor_m (.bvar (.there .here)) (.bvar .here)))))))))))))

theorem trace_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e a n g : Term ℒ Γ Δ .set) :
    (trace_m ω e a n g).satisfies η ↔ trace_l (ω.eval η) (e.eval η) (a.eval η) (n.eval η) (g.eval η) := by
  simp only [trace_m, trace_l, Formula.satisfies, PowerlessNaturalStep.successor_formula_l,
    map_formula_l, value_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

def addition_m {Γ Δ : SortContext ℒ} (ω e a b c : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set (.conj (trace_m (ω.weakenBound SetTheory.SetSort.set) (e.weakenBound SetTheory.SetSort.set)
    (a.weakenBound SetTheory.SetSort.set) (b.weakenBound SetTheory.SetSort.set) (.bvar .here))
    (SecondOrderObjectSyntax.value_m (.bvar .here) (b.weakenBound SetTheory.SetSort.set) (c.weakenBound SetTheory.SetSort.set)))

theorem addition_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e a b c : Term ℒ Γ Δ .set) :
    (addition_m ω e a b c).satisfies η ↔ addition_l (ω.eval η) (e.eval η) (a.eval η) (b.eval η) (c.eval η) := by
  simp only [addition_m, addition_l, Formula.satisfies, trace_formula_l, value_formula_l, Term.eval_weakenBound]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessAdditionFiniteSyntax
