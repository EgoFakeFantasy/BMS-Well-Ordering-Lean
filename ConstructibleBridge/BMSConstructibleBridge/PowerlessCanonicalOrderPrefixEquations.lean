import BMSConstructibleBridge.PowerlessCanonicalOrderRawPrefix
import BMSConstructibleBridge.PowerlessCanonicalOrderOrdinalRestriction

/-! # 任意实际原比较前缀的同步层限制及原方程

只从完整 raw 前缀规格及原图总性推出域包含，再实际限制原层图。
后继的真实前驱与极限的全部 raw 成员都保持在同一内部序数初段。
原父序证书逐值传输，旧数字指标、raw 陪域与编码 K 均不变。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderPrefixEquations

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Ordinal" => SetTheory.Structure.IsOrdinal
  (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱)

theorem exists_l (K : source_coding_l hℳ)
    {t₁ t₂ t₃ Pair Valid B P₀ F G δ W q α p : type_l hℳ}
    (hF : map_l (ℳ := 𝒱) F δ W) (hG : map_l (ℳ := 𝒱) G δ q)
    (hEquations : PowerlessCanonicalOrderOrdinalRestriction.equations_l K
      t₁ t₂ t₃ Pair Valid B P₀ F G)
    (hOrder : ∀ a X P, value_l (ℳ := 𝒱) F a X → value_l (ℳ := 𝒱) G a P →
      wellOrder_l (ℳ := 𝒱) X P)
    (hα : Ordinal α) (hp : PowerlessCanonicalOrderRawPrefix.holds_l (𝒩 := 𝒱) G q α p) :
    ∃ f, map_l (ℳ := 𝒱) f α W ∧
      (∀ a X, value_l (ℳ := 𝒱) f a X ↔ mem_l hℳ a α ∧ value_l (ℳ := 𝒱) F a X) ∧
      PowerlessCanonicalOrderOrdinalRestriction.equations_l K
        t₁ t₂ t₃ Pair Valid B P₀ f p ∧
      ∀ a X P, value_l (ℳ := 𝒱) f a X → value_l (ℳ := 𝒱) p a P →
        wellOrder_l (ℳ := 𝒱) X P := by
  have hSubset := PowerlessCanonicalOrderRawPrefix.subset_l hℳ hG hp
  obtain ⟨f, hf, hRead⟩ := SecondOrderFunctionRestriction.exists_l hℳ hF hSubset
  refine ⟨f, hf, hRead, ?_, ?_⟩
  · intro a X P hX hP
    have ha := ((hRead a X).mp hX).1
    have hFX := ((hRead a X).mp hX).2
    have hGP := ((hp.2 a P).mp hP).2
    rcases hEquations a X P hFX hGP with hZero | hSuccessor | hUnion
    · exact Or.inl hZero
    · obtain ⟨b, Y, Q, hSucc, hY, hQ, hStep⟩ := hSuccessor
      have hb : mem_l hℳ b α := hα.transitive a ha b
        (PowerlessRelativeHierarchyStep.successor_member_l hℳ hSucc)
      exact Or.inr (Or.inl ⟨b, Y, Q, hSucc,
        (hRead b Y).mpr ⟨hb, hY⟩, (hp.2 b Q).mpr ⟨hb, hQ⟩, hStep⟩)
    · refine Or.inr (Or.inr ⟨hUnion.1, ?_, ?_⟩)
      · intro x
        refine (hUnion.2.1 x).trans ?_
        constructor
        · rintro ⟨b, Y, hb, hY, hx⟩
          exact ⟨b, Y, hb, (hRead b Y).mpr ⟨hα.transitive a ha b hb, hY⟩, hx⟩
        · rintro ⟨b, Y, hb, hY, hx⟩
          exact ⟨b, Y, hb, ((hRead b Y).mp hY).2, hx⟩
      · intro x
        refine (hUnion.2.2 x).trans ?_
        constructor
        · rintro ⟨b, Q, hb, hQ, hx⟩
          exact ⟨b, Q, hb, (hp.2 b Q).mpr ⟨hα.transitive a ha b hb, hQ⟩, hx⟩
        · rintro ⟨b, Q, hb, hQ, hx⟩
          exact ⟨b, Q, hb, ((hp.2 b Q).mp hQ).2, hx⟩
  · intro a X P hX hP
    exact hOrder a X P ((hRead a X).mp hX).2 ((hp.2 a P).mp hP).2

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderPrefixEquations
