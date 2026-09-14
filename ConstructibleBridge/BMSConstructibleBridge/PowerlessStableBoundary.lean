import BMSConstructibleBridge.PowerlessStableMinimum

/-!
# κ 以下可变上端点的最小稳定边界

候选下端点须在 κ 中有同层稳定后继；上端点不是预先固定的 β。
纯公式分离与内部正则性给最小候选，不使用外部序数良基性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessStableBoundary

open Logic FirstOrder ThirdOrderSemantics PowerlessStageStability

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def endpoint_l (ω e T t₁ t₂ t₃ κ n α : carrier_l ℳ) : Prop :=
  member_l ℳ α κ ∧ ∃ β, member_l ℳ β κ ∧ stable_l ω e T t₁ t₂ t₃ n α β

def endpoint_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ κ n α : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (s : Term ℒ Γ Δ .set) := s.weakenBound SetTheory.SetSort.set
  .conj (SecondOrderObjectSyntax.member_m α κ) (.existsE .set
    (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (w κ))
      (stable_m (w ω) (w e) (w T) (w t₁) (w t₂) (w t₃) (w n) (w α) (.bvar .here))))

theorem endpoint_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ κ n α : Term ℒ Γ Δ .set) :
    (endpoint_m ω e T t₁ t₂ t₃ κ n α).satisfies η ↔
      endpoint_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
        (κ.eval η) (n.eval η) (α.eval η) := by
  simp only [endpoint_m, endpoint_l, Formula.satisfies, stable_formula_l hℳ,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

def boundary_l (ω e T t₁ t₂ t₃ κ n σ : carrier_l ℳ) : Prop :=
  endpoint_l ω e T t₁ t₂ t₃ κ n σ ∧
    ∀ α, member_l ℳ α σ → ¬endpoint_l ω e T t₁ t₂ t₃ κ n α

def boundary_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ κ n σ : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (s : Term ℒ Γ Δ .set) := s.weakenBound SetTheory.SetSort.set
  .conj (endpoint_m ω e T t₁ t₂ t₃ κ n σ) (.forallE .set
    (.imp (SecondOrderObjectSyntax.member_m (.bvar .here) (w σ))
      (.neg (endpoint_m (w ω) (w e) (w T) (w t₁) (w t₂) (w t₃) (w κ) (w n) (.bvar .here)))))

theorem boundary_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ κ n σ : Term ℒ Γ Δ .set) :
    (boundary_m ω e T t₁ t₂ t₃ κ n σ).satisfies η ↔
      boundary_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
        (κ.eval η) (n.eval η) (σ.eval η) := by
  simp only [boundary_m, boundary_l, Formula.satisfies, endpoint_formula_l hℳ,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

theorem set_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (ω e T t₁ t₂ t₃ κ n : carrier_l ℳ) :
    ∃ C, ∀ α, member_l ℳ α C ↔ endpoint_l ω e T t₁ t₂ t₃ κ n α := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 8 :=
    { bound := Fin.cases ω (Fin.cases e (Fin.cases T (Fin.cases t₁
        (Fin.cases t₂ (Fin.cases t₃ (Fin.cases κ (fun _ => n))))))), free := fun _ => ω }
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] :=
    endpoint_m (.fvar (.there .here))
      (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
      (.fvar .here)
  have h : ∀ α, φ.satisfies ((PowerlessComprehension.env_l η).pushFree α) ↔
      endpoint_l ω e T t₁ t₂ t₃ κ n α := by
    intro α
    rw [endpoint_formula_l hℳ]
    rfl
  obtain ⟨C, hC⟩ := PowerlessComprehension.separation_l hℳ φ η κ
  exact ⟨C, fun α => ⟨fun hx => (h α).mp ((hC α).mp hx).2,
    fun hx => (hC α).mpr ⟨hx.1, (h α).mpr hx⟩⟩⟩

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ n α : carrier_l ℳ} (h : endpoint_l ω e T t₁ t₂ t₃ κ n α) :
    ∃ σ, boundary_l ω e T t₁ t₂ t₃ κ n σ := by
  obtain ⟨C, hC⟩ := set_l hℳ ω e T t₁ t₂ t₃ κ n
  obtain ⟨σ, hσ, h₀⟩ := PowerlessBasic.foundation_l hℳ ⟨α, (hC α).mpr h⟩
  exact ⟨σ, (hC σ).mp hσ, fun γ hγ h₁ => h₀ γ hγ ((hC γ).mpr h₁)⟩

theorem ordinal_l {ω e T t₁ t₂ t₃ κ n σ : carrier_l ℳ}
    (h : boundary_l ω e T t₁ t₂ t₃ κ n σ) : PowerlessOrdinal.ordinal_l σ := by
  obtain ⟨β, _, hβ⟩ := h.1.2
  exact hβ.2.1.2.2.1.1

theorem natural_l {ω e T t₁ t₂ t₃ κ n σ : carrier_l ℳ}
    (h : boundary_l ω e T t₁ t₂ t₃ κ n σ) : member_l ℳ n ω := by
  obtain ⟨β, _, hβ⟩ := h.1.2
  exact hβ.1

theorem lower_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ n σ α : carrier_l ℳ}
    (hσ : boundary_l ω e T t₁ t₂ t₃ κ n σ) (hα : endpoint_l ω e T t₁ t₂ t₃ κ n α) :
    σ = α ∨ member_l ℳ σ α := by
  obtain ⟨β, _, hβ⟩ := hα.2
  rcases PowerlessOrdinalOrder.trichotomy_l hℳ (ordinal_l hσ) hβ.2.1.2.2.1.1 with h | h | h
  · exact Or.inr h
  · exact Or.inl h
  · exact (hσ.2 α h hα).elim

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ n σ τ : carrier_l ℳ}
    (hσ : boundary_l ω e T t₁ t₂ t₃ κ n σ) (hτ : boundary_l ω e T t₁ t₂ t₃ κ n τ) : σ = τ := by
  rcases lower_l hℳ hσ hτ.1 with h | h
  · exact h
  · exact (hτ.2 σ h hσ.1).elim

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessStableBoundary
