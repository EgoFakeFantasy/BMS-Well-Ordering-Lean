import BMSConstructibleBridge.PowerlessBoundaryOrder

/-!
# 所有内部有限层边界的真实集合函数族

函数的定义域是模型的整个 ω，值域限制在 κ；读取恰为该层边界。
不把宿主按层选择的函数冒充模型中的集合图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundaryFamily

open Logic FirstOrder ThirdOrderSemantics PowerlessStableBoundary

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def family_l (ω e T t₁ t₂ t₃ κ F : carrier_l ℳ) : Prop :=
  map_l F ω κ ∧ ∀ n σ, member_l ℳ n ω →
    (value_l F n σ ↔ boundary_l ω e T t₁ t₂ t₃ κ n σ)

def family_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ κ F : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (s : Term ℒ Γ Δ .set) := (s.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .conj (SecondOrderObjectSyntax.map_m F ω κ) (.forallE .set (.forallE .set
    (.imp (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (w ω))
      (.iff (SecondOrderObjectSyntax.value_m (w F) (.bvar (.there .here)) (.bvar .here))
        (boundary_m (w ω) (w e) (w T) (w t₁) (w t₂) (w t₃) (w κ) (.bvar (.there .here)) (.bvar .here))))))

theorem family_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ κ F : Term ℒ Γ Δ .set) :
    (family_m ω e T t₁ t₂ t₃ κ F).satisfies η ↔
      family_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
        (κ.eval η) (F.eval η) := by
  simp only [family_m, family_l, Formula.satisfies, map_formula_l, value_formula_l,
    boundary_formula_l hℳ, SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ F G : carrier_l ℳ}
    (hF : family_l ω e T t₁ t₂ t₃ κ F) (hG : family_l ω e T t₁ t₂ t₃ κ G) : F = G :=
  PowerlessFunction.ext_l hℳ hF.1 hG.1 (fun n hn σ => (hF.2 n σ hn).trans (hG.2 n σ hn).symm)

theorem monotone_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ F m n σ τ : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (hF : family_l ω e T t₁ t₂ t₃ κ F) (hmn : subset_l m n)
    (hσ : value_l F m σ) (hτ : value_l F n τ) : σ = τ ∨ member_l ℳ σ τ :=
  PowerlessBoundaryOrder.monotone_l hℳ hω he hT hmn
    ((hF.2 m σ (PowerlessFunction.value_mem_l hℳ hF.1 hσ).1).mp hσ)
    ((hF.2 n τ (PowerlessFunction.value_mem_l hℳ hF.1 hτ).1).mp hτ)

theorem cutoff_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ F m n σ α β : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (hκ : PowerlessOrdinal.ordinal_l κ) (hF : family_l ω e T t₁ t₂ t₃ κ F)
    (hσ : value_l F n σ) (hα : member_l ℳ α σ) (hβ : member_l ℳ β κ)
    (h : PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ m α β) : member_l ℳ m n :=
  PowerlessBoundaryOrder.cutoff_l hℳ hω he hT hκ
    ((hF.2 n σ (PowerlessFunction.value_mem_l hℳ hF.1 hσ).1).mp hσ) hα hβ h

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundaryFamily
