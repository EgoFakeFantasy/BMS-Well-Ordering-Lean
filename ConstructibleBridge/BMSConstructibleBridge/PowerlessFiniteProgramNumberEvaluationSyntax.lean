import BMSConstructibleBridge.PowerlessFiniteProgramEvaluationSyntax

/-! # 同一原程序枚举的类内数码求值 AST

纯隶属 ℒ，只读取给定 U 的同一图；新自由槽依次为输出、数码，
其他槽保持原序。复用总化求值，包括空词与全部缺省分支。
本模块仅构造纯矩阵及读数，没有假定输出像或无限求值图属于 Class。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteProgramNumberEvaluationSyntax

open Logic FirstOrder ThirdOrderSemantics
open PowerlessFiniteProgramEvaluationSyntax (matrix_m matrix_l matrix_formula_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_l parameters_pushBound_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up t))

def number_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a U : Term ℒ Γ Δ .set) :
    Formula ℒ [] (.set :: .set :: (List.replicate Γ.length .set ++ Δ)) :=
  PowerlessSourceOpening.form_m (show Formula ℒ (.set :: .set :: Γ) Δ from
    .existsE .set <| .conj
      (SecondOrderObjectSyntax.value_m (up₃ U) (.bvar (.there (.there .here))) (.bvar .here))
      (matrix_m false φ (up₃ B) (up₃ C) (up₃ ω) (up₃ Q) (up₃ e)
        (up₃ t₀) (up₃ t₁) (up₃ t₂) (up₃ a) (.bvar .here) (.bvar (.there .here))))

variable {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def number_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒩 [] Δ) (B C ω Q e t₀ t₁ t₂ a U n y : carrier_l 𝒩) : Prop :=
  ∃ p, value_l U n p ∧ matrix_l false φ η B C ω Q e t₀ t₁ t₂ a p y

theorem formula_l {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 Γ Δ)
    (B C ω Q e t₀ t₁ t₂ a U : Term ℒ Γ Δ .set) (n y : carrier_l 𝒩) :
    (number_m φ B C ω Q e t₀ t₁ t₂ a U).satisfies
      (((PowerlessSourceOpening.env_l η).pushFree n).pushFree y) ↔
      number_l φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η) (Q.eval η)
        (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (U.eval η) n y := by
  have hη := PowerlessSourceOpening.formula_l
    (show Formula ℒ (.set :: .set :: Γ) Δ from
      .existsE .set <| .conj
        (SecondOrderObjectSyntax.value_m (up₃ U) (.bvar (.there (.there .here))) (.bvar .here))
        (matrix_m false φ (up₃ B) (up₃ C) (up₃ ω) (up₃ Q) (up₃ e)
          (up₃ t₀) (up₃ t₁) (up₃ t₂) (up₃ a) (.bvar .here) (.bvar (.there .here))))
    ((η.pushBound n).pushBound y)
  simpa only [number_m, number_l, PowerlessSourceOpening.push_l, Formula.satisfies,
    value_formula_l, matrix_formula_l, parameters_pushBound_l, up₃, up, Term.eval_weakenBound,
    Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there] using hη

#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteProgramNumberEvaluationSyntax
