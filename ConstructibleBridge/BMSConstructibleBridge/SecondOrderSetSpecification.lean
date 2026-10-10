import BMSConstructibleBridge.SecondOrderFormulaParameters

/-! # 带任意实际参数的一元集合精确规格

统一把逐数公式写成实际实数的全域成员方程，允许任意二阶量词。只进行
捕获避免替换，不把外部谓词自动视为可理解的模型集合。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSetSpecification

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def body_m {Γ Δ Ξ : SortContext signature_m} (φ : Formula signature_m [] (.num :: Δ))
    (x : Term signature_m Γ Ξ .num) (τ : VariableSubstitution signature_m Δ Γ Ξ) :
    Formula signature_m Γ Ξ :=
  SecondOrderFormulaParameters.formula_m φ (fun v => match v with | .here => x | .there v => τ v)

def formula_m {Γ Δ Ξ : SortContext signature_m} (φ : Formula signature_m [] (.num :: Δ))
    (X : Term signature_m Γ Ξ .set) (τ : VariableSubstitution signature_m Δ Γ Ξ) :
    Formula signature_m Γ Ξ :=
  .forallE .num <| .iff (.rel .mem (.cons (.bvar .here) (.cons (X.weakenBound sort_m.num) .nil)))
    (body_m φ (.bvar .here) (fun v => (τ v).weakenBound sort_m.num))

theorem body_pure_m {Γ Δ Ξ : SortContext signature_m} (φ : Formula signature_m [] (.num :: Δ))
    (x : Term signature_m Γ Ξ .num) (τ : VariableSubstitution signature_m Δ Γ Ξ)
    (hφ : language_m φ = true) (hx : pure_term_m x = true)
    (hτ : SecondOrderSubstitution.images_m τ) : language_m (body_m φ x τ) = true := by
  apply SecondOrderFormulaParameters.pure_m _ _ hφ
  intro s v
  cases v with
  | here => exact hx
  | there v => cases s <;> exact hτ v

theorem pure_m {Γ Δ Ξ : SortContext signature_m} (φ : Formula signature_m [] (.num :: Δ))
    (X : Term signature_m Γ Ξ .set) (τ : VariableSubstitution signature_m Δ Γ Ξ)
    (hφ : language_m φ = true) (hX : pure_term_m X = true)
    (hτ : SecondOrderSubstitution.images_m τ) : language_m (formula_m φ X τ) = true := by
  have hBody := body_pure_m φ (Γ := .num :: Γ) (.bvar .here)
    (fun v => (τ v).weakenBound sort_m.num) hφ rfl
    (by intro s v; exact (SecondOrderSubstitution.term_weaken_m (τ v) sort_m.num).trans (hτ v))
  change ((true && (true && (pure_term_m _ && true))) && language_m _) = true
  rw [hBody, SecondOrderSubstitution.term_weaken_m, hX]
  rfl

theorem body_formula_l {Γ Δ Ξ : SortContext signature_m} (η : Env ℳ Γ Ξ)
    (φ : Formula signature_m [] (.num :: Δ)) (x : Term signature_m Γ Ξ .num)
    (τ : VariableSubstitution signature_m Δ Γ Ξ) : (body_m φ x τ).satisfies η ↔
      φ.satisfies ((SecondOrderRelationSpecification.parameters_l η τ).pushFree (x.eval η)) := by
  rw [body_m, SecondOrderFormulaParameters.formula_l]
  apply Iff.of_eq
  apply congrArg (fun ξ => φ.satisfies ξ)
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    cases v <;> rfl

theorem formula_l {Γ Δ Ξ : SortContext signature_m} (η : Env ℳ Γ Ξ)
    (φ : Formula signature_m [] (.num :: Δ)) (X : Term signature_m Γ Ξ .set)
    (τ : VariableSubstitution signature_m Δ Γ Ξ) : (formula_m φ X τ).satisfies η ↔
      ∀ x, mem_l x (X.eval η) ↔ φ.satisfies ((SecondOrderRelationSpecification.parameters_l η τ).pushFree x) := by
  simp only [formula_m, Formula.satisfies, body_formula_l, Arguments.eval, Term.eval, Term.eval_weakenBound]
  apply forall_congr'
  intro x
  apply iff_congr Iff.rfl
  apply Iff.of_eq
  apply congrArg (fun ξ => φ.satisfies ξ)
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    cases v with
    | here => rfl
    | there v => cases s <;> exact Term.eval_weakenBound _ _ _

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSetSpecification
