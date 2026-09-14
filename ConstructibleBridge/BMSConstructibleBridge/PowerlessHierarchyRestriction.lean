import BMSConstructibleBridge.PowerlessEvaluationHierarchy
import BMSConstructibleBridge.PowerlessOrdinalOrder

/-!
# 层次图的初段限制与跨域相容

实际函数限制不改变任一点的严格前史，故保留同一个累计步骤。
内部递归唯一性随后识别不同序数域上重叠的层次值。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyRestriction

open Logic FirstOrder ThirdOrderSemantics PowerlessEvaluationHierarchy

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ f α β : carrier_l ℳ} (hf : hierarchy_l ω e T t₁ t₂ t₃ f α)
    (hβ : PowerlessOrdinal.ordinal_l β) (hβα : subset_l β α) :
    ∃ g, hierarchy_l ω e T t₁ t₂ t₃ g β ∧ ∀ a A, value_l g a A ↔ member_l ℳ a β ∧ value_l f a A := by
  obtain ⟨R, hF, hS⟩ := hf
  obtain ⟨g, hg, h⟩ := PowerlessRestriction.exists_l hℳ hF hβα
  refine ⟨g, ⟨R, hg, ?_⟩, h⟩
  intro a A hA
  obtain ⟨ha, hA⟩ := (h a A).mp hA
  obtain ⟨H, hH, hY⟩ := hS a A hA
  refine ⟨H, ?_, hY⟩
  intro p
  refine (hH p).trans ?_
  constructor
  · rintro ⟨b, B, hp, hb, hB⟩
    exact ⟨b, B, hp, hb, (h b B).mpr ⟨PowerlessOrdinal.transitive_l hβ a b ha hb, hB⟩⟩
  · rintro ⟨b, B, hp, hb, hB⟩
    exact ⟨b, B, hp, hb, ((h b B).mp hB).2⟩

theorem prefix_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ f g α β : carrier_l ℳ} (hω : omega_l ω)
    (hf : hierarchy_l ω e T t₁ t₂ t₃ f α) (hg : hierarchy_l ω e T t₁ t₂ t₃ g β)
    (hβ : PowerlessOrdinal.ordinal_l β) (hβα : subset_l β α) :
    ∀ a A, value_l g a A ↔ member_l ℳ a β ∧ value_l f a A := by
  obtain ⟨r, hr, h⟩ := exists_l hℳ hf hβ hβα
  obtain ⟨s, _, h₀⟩ := PowerlessEvaluationHierarchy.exists_unique_l hℳ hω hβ e T t₁ t₂ t₃
  have h₁ := (h₀ g hg).trans (h₀ r hr).symm
  exact h₁.symm ▸ h

theorem compatible_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ f g α β : carrier_l ℳ} (hω : omega_l ω)
    (hα : PowerlessOrdinal.ordinal_l α) (hβ : PowerlessOrdinal.ordinal_l β)
    (hf : hierarchy_l ω e T t₁ t₂ t₃ f α) (hg : hierarchy_l ω e T t₁ t₂ t₃ g β)
    {a : carrier_l ℳ} (ha : member_l ℳ a α) (hb : member_l ℳ a β) (A : carrier_l ℳ) :
    value_l f a A ↔ value_l g a A := by
  rcases PowerlessOrdinalOrder.trichotomy_l hℳ hα hβ with h | h | h
  · exact (prefix_l hℳ hω hg hf hα
      (fun x hx => PowerlessOrdinal.transitive_l hβ α x h hx) a A).trans (and_iff_right ha)
  · subst β
    exact (prefix_l hℳ hω hg hf hα (fun _ hx => hx) a A).trans (and_iff_right ha)
  · exact ((prefix_l hℳ hω hf hg hβ
      (fun x hx => PowerlessOrdinal.transitive_l hα β x h hx) a A).trans (and_iff_right hb)).symm

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyRestriction
