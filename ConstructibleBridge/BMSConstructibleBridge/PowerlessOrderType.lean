import BMSConstructibleBridge.PowerlessCollapse
import BMSConstructibleBridge.PowerlessOrdinal

/-! # 每个内部集合良序的内部序型 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessOrderType

open Logic FirstOrder ThirdOrderSemantics PowerlessCollapseSyntax PowerlessOrdinal

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem monotone_l {A R f x y a b : carrier_l ℳ} (hF : collapse_l f A R)
    (hx : member_l ℳ x A) (h : value_l R x y) (ha : value_l f x a) (hb : value_l f y b) :
    member_l ℳ a b := (hF y b hb a).mpr ⟨x, hx, h, ha⟩

theorem injective_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A R f B : carrier_l ℳ} (hR : wellOrder_l A R) (hf : map_l f A B) (hF : collapse_l f A R) :
    ThirdOrderSemantics.injective_l f := by
  intro x z y hx hz
  have hx₀ := (PowerlessFunction.value_mem_l hℳ hf hx).1
  have hz₀ := (PowerlessFunction.value_mem_l hℳ hf hz).1
  rcases hR.2.2.1 x z ⟨hx₀, hz₀⟩ with h | h | h
  · have h₀ := monotone_l hF hx₀ h hx hz
    exact (PowerlessNatural.asymmetry_l hℳ h₀ h₀).elim
  · exact h
  · have h₀ := monotone_l hF hz₀ h hz hx
    exact (PowerlessNatural.asymmetry_l hℳ h₀ h₀).elim

theorem relation_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A R f B x y a b : carrier_l ℳ} (hR : wellOrder_l A R) (hf : map_l f A B)
    (hF : collapse_l f A R) (ha : value_l f x a) (hb : value_l f y b) :
    value_l R x y ↔ member_l ℳ a b := by
  constructor
  · exact fun h => monotone_l hF (PowerlessFunction.value_mem_l hℳ hf ha).1 h ha hb
  · intro h
    obtain ⟨k, _, hk, h₀⟩ := (hF y b hb a).mp h
    have h₁ := injective_l hℳ hR hf hF x k a ha h₀
    exact h₁.symm ▸ hk

theorem transitive_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A R f B x a : carrier_l ℳ} (hR : wellOrder_l A R) (hf : map_l f A B)
    (hF : collapse_l f A R) (ha : value_l f x a) : PowerlessNaturalOrder.transitive_l a := by
  intro b c hb hc
  obtain ⟨y, hy, h₀, h₁⟩ := (hF x a ha b).mp hb
  obtain ⟨z, hz, h₂, h₃⟩ := (hF y b h₁ c).mp hc
  have hx := (PowerlessFunction.value_mem_l hℳ hf ha).1
  exact (hF x a ha c).mpr ⟨z, hz, hR.2.1 z y x ⟨hz, hy, hx⟩ h₂ h₀, h₃⟩

theorem ordinal_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A R f B C : carrier_l ℳ} (hR : wellOrder_l A R) (hf : map_l f A B)
    (hF : collapse_l f A R) (hC : ∀ y, member_l ℳ y C ↔ ∃ x, value_l f x y) :
    PowerlessOrdinal.ordinal_l C := by
  apply PowerlessOrdinal.of_transitive_l hℳ
  · intro a b ha hb
    obtain ⟨x, hx⟩ := (hC a).mp ha
    obtain ⟨y, _, _, hy⟩ := (hF x a hx b).mp hb
    exact (hC b).mpr ⟨y, hy⟩
  · intro a ha
    obtain ⟨x, hx⟩ := (hC a).mp ha
    exact transitive_l hℳ hR hf hF hx
  · intro a b ha hb
    obtain ⟨x, hx⟩ := (hC a).mp ha
    obtain ⟨y, hy⟩ := (hC b).mp hb
    have hx₀ := (PowerlessFunction.value_mem_l hℳ hf hx).1
    have hy₀ := (PowerlessFunction.value_mem_l hℳ hf hy).1
    rcases hR.2.2.1 x y ⟨hx₀, hy₀⟩ with h | h | h
    · exact Or.inl (monotone_l hF hx₀ h hx hy)
    · subst y
      exact Or.inr (Or.inl (PowerlessFunction.value_unique_l hℳ hf hx hy))
    · exact Or.inr (Or.inr (monotone_l hF hy₀ h hy hx))

/-- 实际集合双射将所给良序搬到一个上游定义的内部序数。 -/
theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A R : carrier_l ℳ} (hR : wellOrder_l A R) :
    ∃ f B, PowerlessOrdinal.ordinal_l B ∧ map_l f A B ∧ ThirdOrderSemantics.injective_l f ∧
      (∀ y, member_l ℳ y B ↔ ∃ x, value_l f x y) ∧
      ∀ x y a b, value_l f x a → value_l f y b → (value_l R x y ↔ member_l ℳ a b) := by
  obtain ⟨f, C, hf, hF⟩ := PowerlessCollapse.exists_l hℳ hR
  obtain ⟨B, hB⟩ := PowerlessCoordinates.range_exists_l hℳ f
  exact ⟨f, B, ordinal_l hℳ hR hf hF hB,
    PowerlessFunction.range_l hℳ hf (fun x y hy => (hB y).mpr ⟨x, hy⟩),
    injective_l hℳ hR hf hF, hB, fun _ _ _ _ ha hb => relation_l hℳ hR hf hF ha hb⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessOrderType
