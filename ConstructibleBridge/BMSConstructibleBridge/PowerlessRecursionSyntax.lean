import BMSConstructibleBridge.PowerlessOmegaRecursion

/-! # 内部自然数递归结论的纯公式表示 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRecursionSyntax

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 自由变量依次是函数、内部 ω、零、初值及原算子的参数。 -/
def recursion_m {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ)) :
    Formula ℒ [] (.set :: .set :: .set :: .set :: Γ) :=
  let σ : Substitution ℒ [] (.set :: .set :: Γ)
      [.set, .set, .set, .set, .set] (.set :: .set :: .set :: .set :: Γ) :=
    .map (fun v => nomatch v) (fun {s} v => match s, v with
      | .set, .here => .bvar .here
      | .set, .there .here => .bvar (.there .here)
      | .set, .there (.there v) => .fvar (.there (.there (.there (.there v)))))
  .existsE .set (.conj (SecondOrderObjectSyntax.map_m (.fvar .here) (.fvar (.there .here)) (.bvar .here))
    (.conj (SecondOrderObjectSyntax.value_m (.fvar .here)
      (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here)))))
      (.forallE .set (.forallE .set (.forallE .set (.forallE .set
        (.imp (SecondOrderObjectSyntax.member_m (.bvar (.there (.there (.there .here))))
          (.fvar (.there .here)))
          (.imp (PowerlessNaturalStep.successor_m (.bvar (.there (.there (.there .here))))
            (.bvar (.there (.there .here))))
            (.imp (SecondOrderObjectSyntax.value_m (.fvar .here)
              (.bvar (.there (.there (.there .here)))) (.bvar (.there .here)))
              (.imp (SecondOrderObjectSyntax.value_m (.fvar .here)
                (.bvar (.there (.there .here))) (.bvar .here)) (φ.substitute σ)))))))))))

theorem recursion_formula_l {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (f ω e a : carrier_l ℳ) :
    (recursion_m φ).satisfies (((((PowerlessComprehension.env_l η).pushFree a).pushFree e).pushFree ω).pushFree f) ↔
      PowerlessOmegaRecursion.recursion_l φ η f ω e a := by
  simp only [recursion_m, PowerlessOmegaRecursion.recursion_l, Formula.satisfies,
    PowerlessNaturalStep.successor_formula_l, map_formula_l, value_formula_l,
    Formula.satisfies_substitute, SecondOrderObjectSyntax.member_m, Arguments.eval]
  apply exists_congr
  intro B
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  apply forall_congr'
  intro n
  apply forall_congr'
  intro m
  apply forall_congr'
  intro x
  apply forall_congr'
  intro y
  apply imp_congr_right
  intro _
  apply imp_congr_right
  intro _
  apply imp_congr_right
  intro _
  apply imp_congr_right
  intro _
  apply Iff.of_eq
  apply congrArg (fun η => φ.satisfies η)
  apply Env.ext
  · intro s v
    nomatch v
  · intro s v
    match s, v with
    | .set, .here => rfl
    | .set, .there .here => rfl
    | .set, .there (.there v) => rfl

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRecursionSyntax
