import BMSConstructibleBridge.SecondOrderSections

/-!
# 带参数的内部集合操作公式

操作由实际公式给出，两个集合参数占绑定槽，其余参数保持原排序上下文。
捕获避免替换和参数环境直接复用上游机制，不把任意外部集合关系当作可定义。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSetOperator

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def relation_l {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ)
    (η : Env ℳ [] Δ) (X Y : set_l ℳ) : Prop := Formula.satisfies ((η.pushBound X).pushBound Y) φ

def parameters_l {Γ Δ Ξ : SortContext signature_m} (η : Env ℳ Γ Ξ)
    (ρ : VariableSubstitution signature_m Δ Γ Ξ) : Env ℳ [] Δ where
  boundVal := fun v => nomatch v
  freeVal := fun v => (ρ v).eval η

private def bind {Γ Δ Ξ : SortContext signature_m} (X Y : Term signature_m Γ Ξ .set)
    (ρ : VariableSubstitution signature_m Δ Γ Ξ) : Substitution signature_m [.set, .set] Δ Γ Ξ :=
  .map (fun v => match v with
    | .here => Y
    | .there .here => X) ρ

def formula_m {Γ Δ Ξ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ)
    (X Y : Term signature_m Γ Ξ .set) (ρ : VariableSubstitution signature_m Δ Γ Ξ) :
    Formula signature_m Γ Ξ := φ.substitute (bind X Y ρ)

theorem pure_m {Γ Δ Ξ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ)
    (X Y : Term signature_m Γ Ξ .set) (ρ : VariableSubstitution signature_m Δ Γ Ξ)
    (hφ : language_m φ = true) (hX : pure_term_m X = true) (hY : pure_term_m Y = true)
    (hρ : SecondOrderSubstitution.images_m ρ) : language_m (formula_m φ X Y ρ) = true := by
  refine (SecondOrderSubstitution.form_subst_m φ _ _ ?_ hρ).trans hφ
  intro s v
  match v with
  | .here => exact hY
  | .there .here => exact hX

theorem formula_l {Γ Δ Ξ : SortContext signature_m} (η : Env ℳ Γ Ξ)
    (φ : Formula signature_m [.set, .set] Δ) (X Y : Term signature_m Γ Ξ .set)
    (ρ : VariableSubstitution signature_m Δ Γ Ξ) :
    Formula.satisfies η (formula_m φ X Y ρ) ↔ relation_l φ (parameters_l η ρ) (X.eval η) (Y.eval η) := by
  rw [formula_m, Formula.satisfies_substitute]
  apply Iff.of_eq
  apply congrArg (fun η => Formula.satisfies η φ)
  apply Env.ext
  · intro s v
    match v with
    | .here => rfl
    | .there .here => rfl
  · intro s v
    rfl

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSetOperator
