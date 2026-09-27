import BMSConstructibleBridge.PowerlessStageStabilityOrder

/-!
# 固定上端点下的最小稳定下端点

先在实际上端点集合中分离全部稳定下端点，再以内部正则性取最小元。
这不是全局最小全稳定边界，也不借宿主序数的良基性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessStableMinimum

open Logic FirstOrder ThirdOrderSemantics PowerlessStageStability

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def minimum_l (ω e T t₁ t₂ t₃ n β ξ : carrier_l ℳ) : Prop :=
  stable_l ω e T t₁ t₂ t₃ n ξ β ∧
    ∀ α, member_l ℳ α ξ → ¬stable_l ω e T t₁ t₂ t₃ n α β

def minimum_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ n β ξ : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (s : Term ℒ Γ Δ .set) := s.weakenBound SetTheory.SetSort.set
  .conj (stable_m ω e T t₁ t₂ t₃ n ξ β) (.forallE .set
    (.imp (SecondOrderObjectSyntax.member_m (.bvar .here) (w ξ))
      (.neg (stable_m (w ω) (w e) (w T) (w t₁) (w t₂) (w t₃) (w n) (.bvar .here) (w β)))))

theorem minimum_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ n β ξ : Term ℒ Γ Δ .set) :
    (minimum_m ω e T t₁ t₂ t₃ n β ξ).satisfies η ↔
      minimum_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
        (n.eval η) (β.eval η) (ξ.eval η) := by
  simp only [minimum_m, minimum_l, Formula.satisfies, stable_formula_l hℳ,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

theorem set_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (ω e T t₁ t₂ t₃ n β : carrier_l ℳ) :
    ∃ C, ∀ α, member_l ℳ α C ↔ stable_l ω e T t₁ t₂ t₃ n α β := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 8 :=
    { bound := Fin.cases ω (Fin.cases e (Fin.cases T (Fin.cases t₁
        (Fin.cases t₂ (Fin.cases t₃ (Fin.cases n (fun _ => β))))))), free := fun _ => ω }
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] :=
    stable_m (.fvar (.there .here))
      (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
      (.fvar .here)
      (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
  have h : ∀ α, φ.satisfies ((PowerlessComprehension.env_l η).pushFree α) ↔
      stable_l ω e T t₁ t₂ t₃ n α β := by
    intro α
    rw [stable_formula_l hℳ]
    rfl
  obtain ⟨C, hC⟩ := PowerlessComprehension.separation_l hℳ φ η β
  exact ⟨C, fun α => ⟨fun hx => (h α).mp ((hC α).mp hx).2,
    fun hx => (hC α).mpr ⟨hx.2.1.2.1, (h α).mpr hx⟩⟩⟩

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ n α β : carrier_l ℳ} (h : stable_l ω e T t₁ t₂ t₃ n α β) :
    ∃ ξ, minimum_l ω e T t₁ t₂ t₃ n β ξ := by
  obtain ⟨C, hC⟩ := set_l hℳ ω e T t₁ t₂ t₃ n β
  obtain ⟨ξ, hξ, h₀⟩ := PowerlessBasic.foundation_l hℳ ⟨α, (hC α).mpr h⟩
  exact ⟨ξ, (hC ξ).mp hξ, fun γ hγ h₁ => h₀ γ hγ ((hC γ).mpr h₁)⟩

theorem lower_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ n α β ξ : carrier_l ℳ}
    (hξ : minimum_l ω e T t₁ t₂ t₃ n β ξ) (hα : stable_l ω e T t₁ t₂ t₃ n α β) :
    ξ = α ∨ member_l ℳ ξ α := by
  rcases PowerlessOrdinalOrder.trichotomy_l hℳ hξ.1.2.1.2.2.1.1 hα.2.1.2.2.1.1 with h | h | h
  · exact Or.inr h
  · exact Or.inl h
  · exact (hξ.2 α h hα).elim

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ n β ξ η : carrier_l ℳ}
    (hξ : minimum_l ω e T t₁ t₂ t₃ n β ξ) (hη : minimum_l ω e T t₁ t₂ t₃ n β η) : ξ = η := by
  rcases lower_l hℳ hξ hη.1 with h | h
  · exact h
  · exact (hη.2 ξ h hξ.1).elim

theorem monotone_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ m n β ξ η : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (hmn : subset_l m n) (hξ : minimum_l ω e T t₁ t₂ t₃ m β ξ)
    (hη : minimum_l ω e T t₁ t₂ t₃ n β η) : ξ = η ∨ member_l ℳ ξ η :=
  lower_l hℳ hξ (PowerlessStageStabilityOrder.monotone_l hℳ hω he hT hξ.1.1 hmn hη.1)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessStableMinimum

