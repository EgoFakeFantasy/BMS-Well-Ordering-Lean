import BMSConstructibleBridge.PowerlessRelativeFiniteElementarity

/-! # 同值域与同值参数的有限元素性运输

两侧可有不同自由上下文，只比较实际域及指定参数的求值。
通过原相对化读数运输全部绑定赋值，不展开具体大公式，不要求域传递。
这是原 AST 的语义同余接口，不增加对象理论公理或 Type 层选择。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteElementarityCongruence

open Logic FirstOrder ThirdOrderSemantics
open PowerlessRelativeFiniteElementarity (family_m entry_m form_m entry_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem entry_l {Γ Δ Ε Θ : SortContext ℒ} (φ : Formula ℒ Γ Δ)
    (ζ : Env ℳ [] Ε) (η : Env ℳ [] Θ)
    (I₀ W₀ : Term ℒ [] Ε .set) (τ₀ : Variable Δ .set → Term ℒ [] Ε .set)
    (I₁ W₁ : Term ℒ [] Θ .set) (τ₁ : Variable Δ .set → Term ℒ [] Θ .set)
    (hI : I₀.eval ζ = I₁.eval η) (hW : W₀.eval ζ = W₁.eval η)
    (hτ : ∀ v, (τ₀ v).eval ζ = (τ₁ v).eval η) :
    (entry_m φ I₀ W₀ τ₀).satisfies ζ ↔ (entry_m φ I₁ W₁ τ₁).satisfies η := by
  let ν : Env ℳ [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with | .set => (τ₀ v).eval ζ }
  rw [entry_formula_l φ ζ I₀ W₀ τ₀ ν (fun _ => rfl),
    entry_formula_l φ η I₁ W₁ τ₁ ν (fun v => (hτ v).symm)]
  rw [hI, hW]

/-- 外部有限共同族的全部条目保持，不替换为较小子族。 -/
theorem formula_l {Δ Ε Θ : SortContext ℒ} (Φ : family_m Δ)
    (ζ : Env ℳ [] Ε) (η : Env ℳ [] Θ)
    (I₀ W₀ : Term ℒ [] Ε .set) (τ₀ : Variable Δ .set → Term ℒ [] Ε .set)
    (I₁ W₁ : Term ℒ [] Θ .set) (τ₁ : Variable Δ .set → Term ℒ [] Θ .set)
    (hI : I₀.eval ζ = I₁.eval η) (hW : W₀.eval ζ = W₁.eval η)
    (hτ : ∀ v, (τ₀ v).eval ζ = (τ₁ v).eval η) :
    (form_m Φ I₀ W₀ τ₀).satisfies ζ ↔ (form_m Φ I₁ W₁ τ₁).satisfies η := by
  induction Φ with
  | nil => exact Iff.rfl
  | cons p Φ h =>
    change (_ ∧ _) ↔ (_ ∧ _)
    exact and_congr (entry_l p.2 ζ η I₀ W₀ τ₀ I₁ W₁ τ₁ hI hW hτ) h

#print axioms entry_l
#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteElementarityCongruence
