import BMSConstructibleBridge.PowerlessTriangularFinite
import BMSConstructibleBridge.PowerlessAdditionFiniteSyntax

/-! # 有限三角数计算的原纯语言公式 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessTriangularFiniteSyntax

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def trace_m {Γ Δ : SortContext ℒ} (ω e n g : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) :=
    let t₁ := t.weakenBound SetTheory.SetSort.set
    let t₂ := t₁.weakenBound SetTheory.SetSort.set
    let t₃ := t₂.weakenBound SetTheory.SetSort.set
    let t₄ := t₃.weakenBound SetTheory.SetSort.set
    t₄.weakenBound SetTheory.SetSort.set
  let φ : Formula ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ :=
    .imp (SecondOrderObjectSyntax.member_m (.bvar (.there (.there (.there .here)))) (w n))
      (.imp (PowerlessNaturalStep.successor_m (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here))))
        (.imp (SecondOrderObjectSyntax.value_m (w g) (.bvar (.there (.there (.there .here)))) (.bvar (.there .here)))
          (.imp (SecondOrderObjectSyntax.value_m (w g) (.bvar (.there (.there .here))) (.bvar .here))
            (PowerlessAdditionFiniteSyntax.addition_m (w ω) (w e) (.bvar (.there .here))
              (.bvar (.there (.there .here))) (.bvar .here)))))
  .existsE .set (.conj
    (PowerlessNaturalStep.successor_m (n.weakenBound SetTheory.SetSort.set) (.bvar .here))
    (.conj (SecondOrderObjectSyntax.map_m (g.weakenBound SetTheory.SetSort.set)
      (.bvar .here) (ω.weakenBound SetTheory.SetSort.set))
      (.conj (SecondOrderObjectSyntax.value_m (g.weakenBound SetTheory.SetSort.set)
        (e.weakenBound SetTheory.SetSort.set) (e.weakenBound SetTheory.SetSort.set))
        (.forallE .set (.forallE .set (.forallE .set (.forallE .set φ)))))))

theorem trace_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e n g : Term ℒ Γ Δ .set) :
    (trace_m ω e n g).satisfies η ↔ PowerlessTriangularFinite.trace_l (ω.eval η) (e.eval η) (n.eval η) (g.eval η) := by
  simp only [trace_m, PowerlessTriangularFinite.trace_l, Formula.satisfies, PowerlessNaturalStep.successor_formula_l,
    map_formula_l, ThirdOrderSemantics.value_formula_l, PowerlessAdditionFiniteSyntax.addition_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

def value_m {Γ Δ : SortContext ℒ} (ω e n t : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set (.conj (trace_m (ω.weakenBound SetTheory.SetSort.set) (e.weakenBound SetTheory.SetSort.set)
    (n.weakenBound SetTheory.SetSort.set) (.bvar .here))
    (SecondOrderObjectSyntax.value_m (.bvar .here) (n.weakenBound SetTheory.SetSort.set) (t.weakenBound SetTheory.SetSort.set)))

theorem value_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e n t : Term ℒ Γ Δ .set) :
    (value_m ω e n t).satisfies η ↔ PowerlessTriangularFinite.value_l (ω.eval η) (e.eval η) (n.eval η) (t.eval η) := by
  simp only [value_m, PowerlessTriangularFinite.value_l, Formula.satisfies, trace_formula_l,
    ThirdOrderSemantics.value_formula_l, Term.eval_weakenBound]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessTriangularFiniteSyntax
