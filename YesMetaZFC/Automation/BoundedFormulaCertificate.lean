import YesMetaZFC.Automation.ParameterFusion

/-! # 指定赋值域上的有限有界公式证书

证书仅断言存在一个有限参数环境及 Δ₀ 等价式。独立证书沿参数
拼接组合，不抽取 Type 数据，也不要求任何特定对象理论公理。
-/

namespace YesMetaZFC.Automation.BoundedFormulaCertificate

open Logic FirstOrder

set_option autoImplicit false

universe u v w x

variable {σ : Signature.{u, v, w}} {ℳ : FirstOrder.Structure.{u, v, w, x} σ}
  {ℬ : Formula.LevyBound σ} {Γ Δ : SortContext σ}

def certificate_l (ℬ : Formula.LevyBound σ) (φ : Formula σ Γ Δ)
    (η : Env ℳ [] Δ) (domain : Env ℳ Γ [] → Prop) : Prop :=
  ∃ Ξ, ∃ ψ : Formula σ Γ Ξ, Formula.IsDelta0 ℬ ψ ∧
    ∃ θ : Env ℳ [] Ξ, ∀ (ρ : Env ℳ Γ []), domain ρ →
      (φ.satisfies (ParameterFusion.join_l ρ η) ↔ ψ.satisfies (ParameterFusion.join_l ρ θ))

/-- 真值函数只需保持逐项等价；原公式与有界公式使用同一联结词。 -/
theorem combine_l {φ χ : Formula σ Γ Δ} {η : Env ℳ [] Δ} {domain : Env ℳ Γ [] → Prop}
    (op : {Ξ : SortContext σ} → Formula σ Γ Ξ → Formula σ Γ Ξ → Formula σ Γ Ξ)
    (P : Prop → Prop → Prop)
    (hDelta : ∀ {Ξ} {a b : Formula σ Γ Ξ}, Formula.IsDelta0 ℬ a →
      Formula.IsDelta0 ℬ b → Formula.IsDelta0 ℬ (op a b))
    (hSem : ∀ {Ξ} (a b : Formula σ Γ Ξ) (ζ : Env ℳ Γ Ξ),
      (op a b).satisfies ζ ↔ P (a.satisfies ζ) (b.satisfies ζ))
    (hCongr : ∀ {p q p' q' : Prop}, (p ↔ p') → (q ↔ q') → (P p q ↔ P p' q'))
    (hφ : certificate_l ℬ φ η domain) (hχ : certificate_l ℬ χ η domain) :
    certificate_l ℬ (op φ χ) η domain := by
  obtain ⟨Ξ, ψ, hψ, θ, hφ⟩ := hφ
  obtain ⟨Λ, ξ, hξ, ζ, hχ⟩ := hχ
  refine ⟨Ξ ++ Λ, op (ParameterFusion.left_m ψ) (ParameterFusion.right_m ξ),
    hDelta (ParameterFusion.left_delta_l hψ) (ParameterFusion.right_delta_l hξ),
    ParameterFusion.append_l θ ζ, fun ρ hρ => ?_⟩
  exact (hSem φ χ _).trans ((hCongr
    ((hφ ρ hρ).trans (ParameterFusion.left_formula_l ψ ρ θ ζ).symm)
    ((hχ ρ hρ).trans (ParameterFusion.right_formula_l ξ ρ θ ζ).symm)).trans (hSem _ _ _).symm)

#print axioms combine_l

end YesMetaZFC.Automation.BoundedFormulaCertificate
