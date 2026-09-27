import BMSConstructibleBridge.PowerlessCodedDiagram
import BMSConstructibleBridge.PowerlessFiniteStablePair
import BMSConstructibleBridge.PowerlessGlobalBoundary
import BMSConstructibleBridge.PowerlessSourceStandardBudget

/-!
# 固定好标签类中的最小稳定边界

裸稳定关系的最小端点未必满足反射所需的有限支持。本模块固定一个支持理论的
统一数码 c,N，只在两端均为该理论好标签的稳定对中取最小下端点。
不同层号共用同一好标签类；数码随支持上界变化，关系公式正文不变。
存在性来自实际有限稳定对，最小性来自模型内分离与正则性，不用宿主良基性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessGoodBoundary

open Logic FirstOrder ThirdOrderSemantics PowerlessCodedDiagram

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 同一数码在每个实际层系统上精确表示指定的有限支持理论。 -/
def code_l (ω e T t₁ t₂ t₃ c N : carrier_l ℳ) (l : Nat) : Prop :=
  ∀ {α A S F}, ∀ hA₀ : ∃ x, member_l ℳ x A,
    PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ α A S F →
    (PowerlessCodedStageTheory.holds_l ω e T t₁ t₂ t₃ c N α ↔
      Theory.Models (PowerlessMemberStructure.structure_l A hA₀)
        (Theory.ofList (PowerlessStabilitySupport.basis_m l)))

def stable_l (ω e T t₁ t₂ t₃ c N n α β : carrier_l ℳ) : Prop :=
  good_l ω e T t₁ t₂ t₃ c N α ∧ good_l ω e T t₁ t₂ t₃ c N β ∧
    PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ n α β

def stable_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ c N n α β : Term ℒ Γ Δ .set) :
    Formula ℒ Γ Δ :=
  .conj (good_m ω e T t₁ t₂ t₃ c N α) (.conj (good_m ω e T t₁ t₂ t₃ c N β)
    (PowerlessStageStability.stable_m ω e T t₁ t₂ t₃ n α β))

theorem stable_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ c N n α β : Term ℒ Γ Δ .set) :
    (stable_m ω e T t₁ t₂ t₃ c N n α β).satisfies η ↔
      stable_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
        (c.eval η) (N.eval η) (n.eval η) (α.eval η) (β.eval η) := by
  simp only [stable_m, stable_l, Formula.satisfies, good_formula_l hℳ,
    PowerlessStageStability.stable_formula_l hℳ]

/-- 好标签的统一数码实际供给每个较小层号所需的支持，不另外假定该支持。 -/
theorem models_l {ω e T t₁ t₂ t₃ c N α A S F : carrier_l ℳ} {k l : Nat}
    (hc : code_l ω e T t₁ t₂ t₃ c N l) (hkl : k ≤ l)
    (hα : good_l ω e T t₁ t₂ t₃ c N α) (hA₀ : ∃ x, member_l ℳ x A)
    (hA : PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ α A S F) :
    Theory.Models (PowerlessMemberStructure.structure_l A hA₀)
      (Theory.ofList (PowerlessStabilitySupport.basis_m k)) :=
  PowerlessStabilitySupport.monotone_l hkl ((hc hA₀ hA).mp hα.2.2)

theorem monotone_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ c N m n α β : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (hm : member_l ℳ m ω) (hmn : subset_l m n)
    (h : stable_l ω e T t₁ t₂ t₃ c N n α β) : stable_l ω e T t₁ t₂ t₃ c N m α β :=
  ⟨h.1, h.2.1, PowerlessStageStabilityOrder.monotone_l hℳ hω he hT hm hmn h.2.2⟩

/-- 支持上界以下的每个外部层号，在同一好标签类中都有任意高的稳定对。 -/
theorem pair_exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ c N : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T) {k l : Nat}
    (hc : code_l ω e T t₁ t₂ t₃ c N l) (hkl : k ≤ l)
    (γ : carrier_l ℳ) (hγ : PowerlessOrdinal.ordinal_l γ) :
    ∃ n α β, PowerlessNumeral.numeral_l e k n ∧ member_l ℳ γ α ∧
      stable_l ω e T t₁ t₂ t₃ c N n α β := by
  obtain ⟨m, α, β, A, B, S, R, F, G, hA₀, hB₀, hm, hγα, hA, hB, h𝒜, hℬ, h⟩ :=
    PowerlessFiniteStablePair.supported_l hℳ hω ht hT l γ hγ
  obtain ⟨n, hn⟩ := PowerlessNumeral.exists_l hℳ e k
  have hα : good_l ω e T t₁ t₂ t₃ c N α :=
    ⟨h.2.1.1, h.2.1.2.2.1, (hc hA₀ hA).mpr h𝒜⟩
  have hβ : good_l ω e T t₁ t₂ t₃ c N β :=
    ⟨PowerlessOrdinal.transitive_l h.2.1.2.2.2.1 α ω h.2.1.2.1 h.2.1.1,
      h.2.1.2.2.2, (hc hB₀ hB).mpr hℬ⟩
  exact ⟨n, α, β, hn, hγα, hα, hβ, PowerlessStageStabilityOrder.monotone_l hℳ hω ht.1 hT
    (PowerlessNumeral.natural_l hℳ hω ht.1 hn)
    (PowerlessSourceStandardBudget.numeral_le_subset_l hℳ e hkl hn hm) h⟩

theorem trans_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ c N n α β γ : carrier_l ℳ} (hω : omega_l ω)
    (h₁ : stable_l ω e T t₁ t₂ t₃ c N n α β) (h₂ : stable_l ω e T t₁ t₂ t₃ c N n β γ) :
    stable_l ω e T t₁ t₂ t₃ c N n α γ :=
  ⟨h₁.1, h₂.2.1, PowerlessStageStabilityOrder.trans_l hℳ hω h₁.2.2 h₂.2.2⟩

theorem interpolate_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ c N n α β γ : carrier_l ℳ} (hω : omega_l ω)
    (hαβ : member_l ℳ α β)
    (h₁ : stable_l ω e T t₁ t₂ t₃ c N n α γ) (h₂ : stable_l ω e T t₁ t₂ t₃ c N n β γ) :
    stable_l ω e T t₁ t₂ t₃ c N n α β :=
  ⟨h₁.1, h₂.1, PowerlessStageStabilityOrder.interpolate_l hℳ hω hαβ h₁.2.2 h₂.2.2⟩

theorem zero_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ c N α β : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (hα : good_l ω e T t₁ t₂ t₃ c N α) (hβ : good_l ω e T t₁ t₂ t₃ c N β)
    (hαβ : member_l ℳ α β) : stable_l ω e T t₁ t₂ t₃ c N e α β :=
  ⟨hα, hβ, PowerlessStageStabilityOrder.zero_l hℳ hω ht hT ⟨hα.1, hαβ, hα.2.1, hβ.2.1⟩⟩

def boundary_l (ω e T t₁ t₂ t₃ c N n σ : carrier_l ℳ) : Prop :=
  (∃ β, stable_l ω e T t₁ t₂ t₃ c N n σ β) ∧
    ∀ α, member_l ℳ α σ → ¬∃ β, stable_l ω e T t₁ t₂ t₃ c N n α β

/-- 分离的是有好稳定上端点的标签，而不是好标签的补集。 -/
theorem minimum_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ c N n α β : carrier_l ℳ}
    (h : stable_l ω e T t₁ t₂ t₃ c N n α β) :
    ∃ σ, boundary_l ω e T t₁ t₂ t₃ c N n σ := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 9 :=
    { bound := Fin.cases ω (Fin.cases e (Fin.cases T (Fin.cases t₁
        (Fin.cases t₂ (Fin.cases t₃ (Fin.cases c (Fin.cases N (fun _ => n)))))))), free := fun _ => ω }
  let p (i : Fin 9) : Term ℒ [.set] (.set :: List.replicate 9 .set) .set :=
    .fvar (.there (SetTheory.Definitional.Project.fo_bound_variable i))
  let φ : Formula ℒ [] (.set :: List.replicate 9 .set) :=
    .existsE .set (stable_m (p 0) (p 1) (p 2) (p 3) (p 4) (p 5) (p 6) (p 7) (p 8)
      (.fvar .here) (.bvar .here))
  have hφ : ∀ ξ, φ.satisfies ((PowerlessComprehension.env_l η).pushFree ξ) ↔
      ∃ γ, stable_l ω e T t₁ t₂ t₃ c N n ξ γ := by
    intro ξ
    change (∃ γ, (stable_m _ _ _ _ _ _ _ _ _ _ _).satisfies _) ↔ _
    simp only [stable_formula_l hℳ]
    rfl
  obtain ⟨C, hC⟩ := PowerlessComprehension.separation_l hℳ φ η β
  obtain ⟨σ, hσ, h₀⟩ := PowerlessBasic.foundation_l hℳ
    ⟨α, (hC α).mpr ⟨h.2.2.2.1.2.1, (hφ α).mpr ⟨β, h⟩⟩⟩
  have hσβ := ((hC σ).mp hσ).1
  refine ⟨σ, (hφ σ).mp ((hC σ).mp hσ).2, ?_⟩
  intro ξ hξ h₁
  exact h₀ ξ hξ ((hC ξ).mpr
    ⟨PowerlessOrdinal.transitive_l h.2.1.2.1.1 σ ξ hσβ hξ, (hφ ξ).mpr h₁⟩)

/-- 边界以下两端均为好标签的稳定边，其层号严格小于边界层号。 -/
theorem cutoff_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ c N n k σ α β : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (hσ : boundary_l ω e T t₁ t₂ t₃ c N n σ) (hα : member_l ℳ α σ)
    (h : stable_l ω e T t₁ t₂ t₃ c N k α β) : member_l ℳ k n := by
  obtain ⟨γ, hγ⟩ := hσ.1
  rcases PowerlessNaturalCompare.compare_l hℳ hω k h.2.2.1 n hγ.2.2.1 with h₀ | rfl | h₀
  · exact h₀
  · exact (hσ.2 α hα ⟨β, h⟩).elim
  · have hnk : subset_l n k := fun x hx =>
      PowerlessNaturalOrder.member_transitive_l hℳ hω k h.2.2.1 n x h₀ hx
    exact (hσ.2 α hα ⟨β, monotone_l hℳ hω he hT hγ.2.2.1 hnk h⟩).elim

theorem lower_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ c N n σ α β : carrier_l ℳ}
    (hσ : boundary_l ω e T t₁ t₂ t₃ c N n σ)
    (hα : stable_l ω e T t₁ t₂ t₃ c N n α β) : σ = α ∨ member_l ℳ σ α := by
  obtain ⟨γ, hγ⟩ := hσ.1
  rcases PowerlessOrdinalOrder.trichotomy_l hℳ hγ.1.2.1.1 hα.1.2.1.1 with h | h | h
  · exact Or.inr h
  · exact Or.inl h
  · exact (hσ.2 α h ⟨β, hα⟩).elim

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ c N n σ τ : carrier_l ℳ}
    (hσ : boundary_l ω e T t₁ t₂ t₃ c N n σ)
    (hτ : boundary_l ω e T t₁ t₂ t₃ c N n τ) : σ = τ := by
  obtain ⟨β, hβ⟩ := hτ.1
  rcases lower_l hℳ hσ hβ with h | h
  · exact h
  · exact (hτ.2 σ h hσ.1).elim

theorem boundary_monotone_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ c N m n σ τ : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (hmn : subset_l m n) (hσ : boundary_l ω e T t₁ t₂ t₃ c N m σ)
    (hτ : boundary_l ω e T t₁ t₂ t₃ c N n τ) : σ = τ ∨ member_l ℳ σ τ := by
  obtain ⟨α, hα⟩ := hσ.1
  obtain ⟨β, hβ⟩ := hτ.1
  exact lower_l hℳ hσ (monotone_l hℳ hω he hT hα.2.2.1 hmn hβ)

/-- 固定一次支持数码后，所有较小外部层号均有同一好标签类中的最小边界。 -/
theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T) (l : Nat) :
    ∃ c N, member_l ℳ c ω ∧ member_l ℳ N ω ∧ code_l ω e T t₁ t₂ t₃ c N l ∧
      ∀ k ≤ l, ∃ n σ, PowerlessNumeral.numeral_l e k n ∧ boundary_l ω e T t₁ t₂ t₃ c N n σ := by
  obtain ⟨c, N, hc, hN, h⟩ := PowerlessCodedStageTheory.code_l hℳ hω ht hT
    (PowerlessStabilitySupport.basis_m l)
  refine ⟨c, N, hc, hN, h, ?_⟩
  intro k hkl
  obtain ⟨n, α, β, hn, _, hαβ⟩ := pair_exists_l hℳ hω ht hT h hkl ω
    (PowerlessOmegaOrdinal.ordinal_l hℳ hω)
  obtain ⟨σ, hσ⟩ := minimum_l hℳ hαβ
  exact ⟨n, σ, hn, hσ⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessGoodBoundary
