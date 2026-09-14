import BMSConstructibleBridge.PowerlessCoordinates
import BMSConstructibleBridge.PowerlessOrdinalOrder

/-!
# 实际序数族的精确上确界

对函数值域取并，保留精确成员式。序数性、最小上界及严格有界族的
上确界仍落在原序数内，都只从实际图和对象层序数性质推出。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessOrdinalSupremum

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def supremum_l (f ξ : carrier_l ℳ) : Prop :=
  ∀ x, member_l ℳ x ξ ↔ ∃ n a, value_l f n a ∧ member_l ℳ x a

def supremum_m {Γ Δ : SortContext ℒ} (f ξ : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.iff (SecondOrderObjectSyntax.member_m (.bvar .here) (ξ.weakenBound SetTheory.SetSort.set))
    (.existsE .set (.existsE .set (.conj (SecondOrderObjectSyntax.value_m
      (((f.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set)
      (.bvar (.there .here)) (.bvar .here))
      (SecondOrderObjectSyntax.member_m (.bvar (.there (.there .here))) (.bvar .here))))))

theorem supremum_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (f ξ : Term ℒ Γ Δ .set) :
    (supremum_m f ξ).satisfies η ↔ supremum_l (f.eval η) (ξ.eval η) := by
  simp only [supremum_m, supremum_l, Formula.satisfies, value_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (f : carrier_l ℳ) :
    ∃ ξ, supremum_l f ξ := by
  obtain ⟨R, hR⟩ := PowerlessCoordinates.range_exists_l hℳ f
  obtain ⟨ξ, hξ⟩ := PowerlessBasic.union_l hℳ R
  refine ⟨ξ, fun x => (hξ x).trans ?_⟩
  constructor
  · rintro ⟨a, ha, hx⟩
    obtain ⟨n, ha⟩ := (hR a).mp ha
    exact ⟨n, a, ha, hx⟩
  · rintro ⟨n, a, ha, hx⟩
    exact ⟨a, (hR a).mpr ⟨n, ha⟩, hx⟩

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {f ξ μ : carrier_l ℳ} (hξ : supremum_l f ξ) (hμ : supremum_l f μ) : ξ = μ :=
  (PowerlessTheory.ext_l hℳ).eq_of_same_members ξ μ (fun x => (hξ x).trans (hμ x).symm)

theorem upper_l {f ξ n a : carrier_l ℳ} (hξ : supremum_l f ξ) (ha : value_l f n a) : subset_l a ξ :=
  fun x hx => (hξ x).mpr ⟨n, a, ha, hx⟩

theorem least_l {f ξ B : carrier_l ℳ} (hξ : supremum_l f ξ)
    (hB : ∀ n a, value_l f n a → subset_l a B) : subset_l ξ B := by
  intro x hx
  obtain ⟨n, a, ha, hx⟩ := (hξ x).mp hx
  exact hB n a ha x hx

theorem subset_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {κ A f ξ : carrier_l ℳ} (hκ : PowerlessOrdinal.ordinal_l κ) (hf : map_l f A κ)
    (hξ : supremum_l f ξ) : ThirdOrderSemantics.subset_l ξ κ :=
  least_l hξ (fun _ a ha x hx => PowerlessOrdinal.transitive_l hκ a x (PowerlessFunction.value_mem_l hℳ hf ha).2 hx)

theorem ordinal_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {κ A f ξ : carrier_l ℳ} (hκ : PowerlessOrdinal.ordinal_l κ) (hf : map_l f A κ)
    (hξ : supremum_l f ξ) : PowerlessOrdinal.ordinal_l ξ := by
  have h := subset_l hℳ hκ hf hξ
  apply PowerlessOrdinal.of_transitive_l hℳ
  · intro x y hx hy
    obtain ⟨n, a, ha, hx⟩ := (hξ x).mp hx
    exact (hξ y).mpr ⟨n, a, ha, PowerlessOrdinal.transitive_l
      (PowerlessOrdinal.mem_l hκ (PowerlessFunction.value_mem_l hℳ hf ha).2) x y hx hy⟩
  · exact fun x hx => PowerlessOrdinal.transitive_l (PowerlessOrdinal.mem_l hκ (h x hx))
  · exact fun x y hx hy => PowerlessOrdinal.compare_l hℳ hκ (h x hx) (h y hy)

theorem member_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {κ A f ξ b : carrier_l ℳ} (hκ : PowerlessOrdinal.ordinal_l κ) (hf : map_l f A κ)
    (hξ : supremum_l f ξ) (hb : ThirdOrderSemantics.member_l ℳ b κ)
    (h : ∀ n a, value_l f n a → ThirdOrderSemantics.member_l ℳ a b) : ThirdOrderSemantics.member_l ℳ ξ κ := by
  have hb₀ := PowerlessOrdinal.mem_l hκ hb
  have h₀ := least_l hξ (fun n a ha x hx => PowerlessOrdinal.transitive_l hb₀ a x (h n a ha) hx)
  rcases PowerlessOrdinalOrder.trichotomy_l hℳ (ordinal_l hℳ hκ hf hξ) hb₀ with h₁ | h₁ | h₁
  · exact PowerlessOrdinal.transitive_l hκ b ξ hb h₁
  · exact h₁.symm ▸ hb
  · exact (PowerlessNatural.asymmetry_l hℳ (h₀ b h₁) (h₀ b h₁)).elim

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessOrdinalSupremum
