import BMSConstructibleBridge.ThirdOrderCantor
import BMSConstructibleBridge.PowerlessOrderType
import BMSConstructibleBridge.PowerlessComposition
import BMSConstructibleBridge.PowerlessOrdinalOrder

/-!
# 三阶工作背景中的首个不可数序数

良序化已经给定的 P(ω)，取内部序型，再分离出其中的最小不可数序数。
不借用宿主 ω₁，不先假设可数关系编码空间，也不在此宣称正则性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderOmegaOne

open Logic FirstOrder ThirdOrderSemantics PowerlessOrdinal

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def countable_l (ω A : carrier_l ℳ) : Prop := ∃ f, map_l f A ω ∧ injective_l f

def countable_m {Γ Δ : SortContext ℒ} (ω A : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set (.conj (SecondOrderObjectSyntax.map_m (.bvar .here)
    (A.weakenBound SetTheory.SetSort.set) (ω.weakenBound SetTheory.SetSort.set))
    (SecondOrderObjectSyntax.injective_m (.bvar .here)))

theorem countable_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω A : Term ℒ Γ Δ .set) :
    (countable_m ω A).satisfies η ↔ countable_l (ω.eval η) (A.eval η) := by
  simp only [countable_m, countable_l, Formula.satisfies, map_formula_l, injective_formula_l,
    Term.eval_weakenBound]
  rfl

def first_l (ω κ : carrier_l ℳ) : Prop :=
  ordinal_l κ ∧ ¬countable_l ω κ ∧ ∀ a, member_l ℳ a κ → countable_l ω a

def first_m {Γ Δ : SortContext ℒ} (ω κ : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (ordinal_m κ) (.conj (.neg (countable_m ω κ))
    (.forallE .set (.imp (SecondOrderObjectSyntax.member_m (.bvar .here) (κ.weakenBound SetTheory.SetSort.set))
      (countable_m (ω.weakenBound SetTheory.SetSort.set) (.bvar .here)))))

theorem first_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω κ : Term ℒ Γ Δ .set) :
    (first_m ω κ).satisfies η ↔ first_l (ω.eval η) (κ.eval η) := by
  simp only [first_m, first_l, Formula.satisfies, ordinal_formula_l hℳ, countable_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

theorem uncountable_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω p R : carrier_l ℳ} (hp : power_l ω p) (hR : wellOrder_l p R) :
    ∃ a, ordinal_l a ∧ ¬countable_l ω a := by
  obtain ⟨f, a, ha, hf, h₀, _⟩ := PowerlessOrderType.exists_l hℳ hR
  refine ⟨a, ha, ?_⟩
  rintro ⟨g, hg, h₁⟩
  obtain ⟨h, hH, h₂⟩ := PowerlessComposition.exists_l hℳ hf hg
  exact ThirdOrderCantor.no_injection_l hℳ hp
    ⟨h, hH, PowerlessComposition.injective_l h₀ h₁ h₂⟩

theorem minimum_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω a : carrier_l ℳ} (ha : ordinal_l a) (h : ¬countable_l ω a) :
    ∃ κ, first_l ω κ := by
  obtain ⟨S, hS⟩ := PowerlessNatural.successor_exists_l hℳ a
  have h₀ := PowerlessOrdinalOrder.successor_l hℳ ha hS
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 1 :=
    { bound := fun _ => ω, free := fun _ => a }
  let φ : Formula ℒ [] [.set, .set] :=
    .neg (countable_m (.fvar (.there .here)) (.fvar .here))
  have h₁ : ∀ x, φ.satisfies ((PowerlessComprehension.env_l η).pushFree x) ↔ ¬countable_l ω x := by
    intro x
    simp only [φ, Formula.satisfies, countable_formula_l]
    rfl
  obtain ⟨C, hC⟩ := PowerlessComprehension.separation_l hℳ φ η S
  have h₂ : ∀ x, member_l ℳ x C ↔ member_l ℳ x S ∧ ¬countable_l ω x :=
    fun x => (hC x).trans (and_congr Iff.rfl (h₁ x))
  obtain ⟨κ, hκ, h₃⟩ := h₀.wellOrder.least C (fun x hx => ((h₂ x).mp hx).1)
    ⟨a, (h₂ a).mpr ⟨(hS a).mpr (Or.inr rfl), h⟩⟩
  have h₄ := (h₂ κ).mp hκ
  refine ⟨κ, mem_l h₀ h₄.1, h₄.2, ?_⟩
  intro b hb
  by_contra h₅
  have hb₀ := PowerlessOrdinal.transitive_l h₀ κ b h₄.1 hb
  rcases h₃ b ((h₂ b).mpr ⟨hb₀, h₅⟩) with h₆ | h₆
  · have h₇ := (PowerlessTheory.ext_l hℳ).eq_of_same_members κ b h₆
    have h₈ : member_l ℳ b b := h₇ ▸ hb
    exact PowerlessNatural.asymmetry_l hℳ h₈ h₈
  · exact PowerlessNatural.asymmetry_l hℳ hb h₆

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω κ ξ : carrier_l ℳ} (hκ : first_l ω κ) (hξ : first_l ω ξ) : κ = ξ := by
  rcases PowerlessOrdinalOrder.trichotomy_l hℳ hκ.1 hξ.1 with h | h | h
  · exact (hκ.2.1 (hξ.2.2 κ h)).elim
  · exact h
  · exact (hξ.2.1 (hκ.2.2 ξ h)).elim

/-- 首个不可数序数只需指定的幂集及其良序，不需全集规模界。 -/
theorem of_power_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω p R : carrier_l ℳ} (hp : power_l ω p) (hR : wellOrder_l p R) : ∃ κ, first_l ω κ := by
  obtain ⟨a, ha, h⟩ := uncountable_l hℳ hp hR
  exact minimum_l hℳ ha h

theorem exists_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m) :
    ∃ ω κ : carrier_l ℳ, omega_l ω ∧ first_l ω κ := by
  obtain ⟨ω, p, hω, hp⟩ := ThirdOrderSemantics.reals_formula_l.mp (ThirdOrderTheory.reals_l hℳ)
  obtain ⟨R, hR⟩ := ThirdOrderSemantics.choice_l hℳ p
  obtain ⟨κ, hκ⟩ := of_power_l (ThirdOrderTheory.core_l hℳ) hp hR
  exact ⟨ω, κ, hω, hκ⟩

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderOmegaOne
