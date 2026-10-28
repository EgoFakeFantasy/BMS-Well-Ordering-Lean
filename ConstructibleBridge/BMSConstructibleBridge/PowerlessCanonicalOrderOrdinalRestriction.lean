import BMSConstructibleBridge.PowerlessCanonicalOrderOrdinalRecursion
import BMSConstructibleBridge.SecondOrderFunctionRestriction

/-! # 同一规范序历史的实际序数初段

对象语言为纯隶属 ℒ，背景为原 Z₂ 图商。原层历史及比较历史同时限制到
内部序数 β，原数字指标及陪域不变。极限并集量化所有 raw 成员；序数
传递性只保证真正前驱仍在 β 中，不使用模型序数的外部良基性。

结果为两张实际干净函数图与完整递归方程，尚不声称它们属于 Class 或
指定层。后续预算归纳必须实际证明这些成员界；本模块不消去枚举族缺口。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderOrdinalRestriction

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

private abbrev zeroCode_l (K : source_coding_l hℳ) :=
  (numberCode_l K (SecondOrderModel.zero_l ℳ)).val

def equations_l (K : source_coding_l hℳ)
    (t₁ t₂ t₃ Pair Valid B P₀ f g : type_l hℳ) : Prop :=
  ∀ a X P, value_l (ℳ := 𝒱) f a X → value_l (ℳ := 𝒱) g a P →
    (PowerlessRelativeHierarchySemantics.empty_l hℳ a ∧ X = B ∧ P = P₀) ∨
      (∃ b Y Q, PowerlessRelativeHierarchySemantics.successor_l hℳ b a ∧
        value_l (ℳ := 𝒱) f b Y ∧ value_l (ℳ := 𝒱) g b Q ∧
        SecondOrderCanonicalOrderUniform.step_l (ℳ₀ := 𝒱) K.omega Y Q (zeroCode_l K)
          t₁ t₂ t₃ Pair Valid X P) ∨
      (PowerlessRelativeHierarchySemantics.limit_l hℳ a ∧
        PowerlessRelativeHierarchySemantics.union_l hℳ f a X ∧
        PowerlessRelativeHierarchySemantics.union_l hℳ g a P)

/-- 取得原历史的两张实际初段图，而非只提供外部限制函数。 -/
theorem exists_l (K : source_coding_l hℳ)
    {t₁ t₂ t₃ Pair Valid B P₀ A F r I J T G q Pord β : type_l hℳ}
    (h : SecondOrderCanonicalLevelSyntax.history_l K.omega (zeroCode_l K)
      t₁ t₂ t₃ Pair Valid B P₀ A F r I J T G q)
    (hRead : PowerlessCanonicalOrderOrdinalHistory.spec_l A I J G Pord)
    (hMap : map_l (ℳ := 𝒱) Pord A q)
    (hBound : ∀ p, mem_l hℳ p P₀ → ∃ x y,
      mem_l hℳ x B ∧ mem_l hℳ y B ∧ SecondOrderPairObjects.ordered_l hℳ x y p)
    (hβ : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) β)
    (hβα : ∀ a, mem_l hℳ a β → mem_l hℳ a A) :
    ∃ f g, map_l (ℳ := 𝒱) f β r ∧ map_l (ℳ := 𝒱) g β q ∧
      (∀ a X, value_l (ℳ := 𝒱) f a X ↔ mem_l hℳ a β ∧ value_l (ℳ := 𝒱) F a X) ∧
      (∀ a P, value_l (ℳ := 𝒱) g a P ↔ mem_l hℳ a β ∧ value_l (ℳ := 𝒱) Pord a P) ∧
      equations_l K t₁ t₂ t₃ Pair Valid B P₀ f g := by
  obtain ⟨f, hf, hFRead⟩ := SecondOrderFunctionRestriction.exists_l hℳ h.configuration.hierarchy.1 hβα
  obtain ⟨g, hg, hGRead⟩ := SecondOrderFunctionRestriction.exists_l hℳ hMap hβα
  refine ⟨f, g, hf, hg, hFRead, hGRead, ?_⟩
  intro a X P hFX hP
  have ha := ((hFRead a X).mp hFX).1
  have hFXOld := ((hFRead a X).mp hFX).2
  have hPOld := ((hGRead a P).mp hP).2
  rcases h.configuration.hierarchy.2 a X ⟨hβα a ha, hFXOld⟩ with
    ⟨hEmpty, _⟩ | ⟨b, _, hSucc, _, _⟩ | ⟨hLimit, hUnion⟩
  · have hZero := PowerlessCanonicalOrderOrdinalRecursion.zero_l K h hRead hFXOld hPOld hEmpty
    exact Or.inl ⟨hEmpty, hZero⟩
  · obtain ⟨Y, Q, hY, hQ, hStep⟩ :=
      PowerlessCanonicalOrderOrdinalRecursion.successor_l K h hRead hFXOld hPOld hSucc
    have hbβ : mem_l hℳ b β := hβ.transitive a ha b
      (PowerlessRelativeHierarchyStep.successor_member_l hℳ hSucc)
    exact Or.inr (Or.inl ⟨b, Y, Q, hSucc,
      (hFRead b Y).mpr ⟨hbβ, hY⟩, (hGRead b Q).mpr ⟨hbβ, hQ⟩, hStep⟩)
  · have hPUnion := PowerlessCanonicalOrderOrdinalRecursion.limit_l K h hRead hBound hPOld hLimit
    refine Or.inr (Or.inr ⟨hLimit, ?_, ?_⟩)
    · intro x
      refine (hUnion x).trans ?_
      constructor
      · rintro ⟨b, Y, hb, hY, hx⟩
        exact ⟨b, Y, hb, (hFRead b Y).mpr ⟨hβ.transitive a ha b hb, hY⟩, hx⟩
      · rintro ⟨b, Y, hb, hY, hx⟩
        exact ⟨b, Y, hb, ((hFRead b Y).mp hY).2, hx⟩
    · intro p
      refine (hPUnion p).trans ?_
      constructor
      · rintro ⟨b, Q, hb, hQ, hp⟩
        exact ⟨b, Q, hb, (hGRead b Q).mpr ⟨hβ.transitive a ha b hb, hQ⟩, hp⟩
      · rintro ⟨b, Q, hb, hQ, hp⟩
        exact ⟨b, Q, hb, ((hGRead b Q).mp hQ).2, hp⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderOrdinalRestriction
