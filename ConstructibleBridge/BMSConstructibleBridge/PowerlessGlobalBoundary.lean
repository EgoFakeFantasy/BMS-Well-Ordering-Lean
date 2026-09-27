import BMSConstructibleBridge.PowerlessStableMinimum

/-!
# 对全部上端点取最小稳定下端点

从任一实际稳定对出发，在其上端点中分离“具有某个稳定上端点”的下端点。
正则性给出全局最小下端点；候选上端点不受分离载体限制。
这一步不证明稳定对存在，也不假定模型在外部良基。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessGlobalBoundary

open Logic FirstOrder ThirdOrderSemantics PowerlessStageStability

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def boundary_l (ω e T t₁ t₂ t₃ n σ : carrier_l ℳ) : Prop :=
  (∃ β, stable_l ω e T t₁ t₂ t₃ n σ β) ∧
    ∀ α, member_l ℳ α σ → ¬∃ β, stable_l ω e T t₁ t₂ t₃ n α β

/-- 已有一个稳定对时，其下端点的全局最小者存在。 -/
theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ n α β : carrier_l ℳ}
    (h : stable_l ω e T t₁ t₂ t₃ n α β) :
    ∃ σ, boundary_l ω e T t₁ t₂ t₃ n σ := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 7 :=
    { bound := Fin.cases ω (Fin.cases e (Fin.cases T (Fin.cases t₁
        (Fin.cases t₂ (Fin.cases t₃ (fun _ => n)))))), free := fun _ => ω }
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] :=
    .existsE .set (stable_m (.fvar (.there .here))
      (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
      (.fvar .here) (.bvar .here))
  have hφ : ∀ ξ, φ.satisfies ((PowerlessComprehension.env_l η).pushFree ξ) ↔
      ∃ γ, stable_l ω e T t₁ t₂ t₃ n ξ γ := by
    intro ξ
    change (∃ γ, (stable_m _ _ _ _ _ _ _ _ _).satisfies _) ↔ _
    simp only [stable_formula_l hℳ]
    rfl
  obtain ⟨C, hC⟩ := PowerlessComprehension.separation_l hℳ φ η β
  obtain ⟨σ, hσ, h₀⟩ := PowerlessBasic.foundation_l hℳ
    ⟨α, (hC α).mpr ⟨h.2.1.2.1, (hφ α).mpr ⟨β, h⟩⟩⟩
  have hσβ := ((hC σ).mp hσ).1
  refine ⟨σ, (hφ σ).mp ((hC σ).mp hσ).2, ?_⟩
  intro ξ hξ h₁
  exact h₀ ξ hξ ((hC ξ).mpr
    ⟨PowerlessOrdinal.transitive_l h.2.1.2.2.2.1 σ ξ hσβ hξ, (hφ ξ).mpr h₁⟩)

/-- 边界以下的稳定层号严格低于边界层号，上端点无需固定。 -/
theorem cutoff_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ n k σ α β : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (hσ : boundary_l ω e T t₁ t₂ t₃ n σ) (hα : member_l ℳ α σ)
    (h : stable_l ω e T t₁ t₂ t₃ k α β) : member_l ℳ k n := by
  obtain ⟨γ, hγ⟩ := hσ.1
  rcases PowerlessNaturalCompare.compare_l hℳ hω k h.1 n hγ.1 with h₀ | rfl | h₀
  · exact h₀
  · exact (hσ.2 α hα ⟨β, h⟩).elim
  · have hnk : subset_l n k := fun x hx =>
      PowerlessNaturalOrder.member_transitive_l hℳ hω k h.1 n x h₀ hx
    exact (hσ.2 α hα ⟨β,
      PowerlessStageStabilityOrder.monotone_l hℳ hω he hT hγ.1 hnk h⟩).elim

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessGlobalBoundary
