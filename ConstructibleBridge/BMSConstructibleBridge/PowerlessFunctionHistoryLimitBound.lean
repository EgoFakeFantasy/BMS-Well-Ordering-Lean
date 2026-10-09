import BMSConstructibleBridge.PowerlessFunctionHistoryAgreement
import BMSConstructibleBridge.PowerlessHierarchyLightHistoryLimitPrefixBound

/-! # 单值后继历史的精确极限前缀界

同一后继图的单值性代替原 Def 读数。全部早期完整前缀已落入同一具体母集
时，原纯 Δ₀ 切片给出前缀族，再由相容性证明其并恰为原历史。两次实际
Def 只用于界定集合，不把后继算子误换为 Def，也不使用 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFunctionHistoryLimitBound

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)
open PowerlessHierarchyLightHistoryLimitPrefixBound (body_m body_delta_l body_reading_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Ordinal" => SetTheory.Structure.IsOrdinal
  (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱)

/-- 全部 raw 有序对，而非仅母层中可见的成员，具有精确并读数。 -/
theorem union_l {X D W α C f H : type_l hℳ}
    (hD : PowerlessFunctionHistoryAgreement.functional_l hℳ D)
    (hα : Ordinal α) (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ α)
    (hf : PowerlessHierarchyLightHistory.history_l hℳ X D α W f)
    (hH : ∀ g : type_l hℳ, mem_l hℳ g H ↔ mem_l hℳ g C ∧
      ∃ β, mem_l hℳ β α ∧ PowerlessHierarchyLightHistory.history_l hℳ X D β W g)
    (hCover : ∀ β, mem_l hℳ β α → ∃ g, mem_l hℳ g C ∧
      PowerlessHierarchyLightHistory.history_l hℳ X D β W g) :
    ∀ p : type_l hℳ, mem_l hℳ p f ↔ ∃ g, mem_l hℳ g H ∧ mem_l hℳ p g := by
  intro p
  constructor
  · intro hp
    obtain ⟨i, y, hi, _hy, hPair⟩ := hf.1.1 p hp
    obtain ⟨β, hβ, hiβ⟩ := hLimit.2 i hi
    obtain ⟨g, hgC, hg⟩ := hCover β hβ
    have hβOrd : Ordinal β := SetTheory.Structure.IsOrdinal.mem hα hβ
    obtain ⟨z, ⟨_hzW, hValue⟩, _⟩ := hg.1.2 i hiβ
    have hyz : y = z := PowerlessFunctionHistoryAgreement.agreement_l hℳ hD hα hβOrd
      hf hg i ⟨hi, hiβ⟩ y z ⟨⟨p, hp, hPair⟩, hValue⟩
    subst z
    obtain ⟨q, hq, hPair'⟩ := hValue
    have hqp : q = p := SecondOrderPairObjects.ordered_unique_l hℳ hPair' hPair
    exact ⟨g, (hH g).mpr ⟨hgC, β, hβ, hg⟩, hqp ▸ hq⟩
  · rintro ⟨g, hgH, hpg⟩
    obtain ⟨_hgC, β, hβ, hg⟩ := (hH g).mp hgH
    obtain ⟨i, y, hiβ, _hy, hPair⟩ := hg.1.1 p hpg
    have hi : mem_l hℳ i α := hα.transitive β hβ i hiβ
    have hβOrd : Ordinal β := SetTheory.Structure.IsOrdinal.mem hα hβ
    obtain ⟨z, ⟨_hzW, hValue⟩, _⟩ := hf.1.2 i hi
    have hzy : z = y := PowerlessFunctionHistoryAgreement.agreement_l hℳ hD hα hβOrd
      hf hg i ⟨hi, hiβ⟩ z y ⟨hValue, ⟨p, hpg, hPair⟩⟩
    subst z
    obtain ⟨q, hq, hPair'⟩ := hValue
    have hqp : q = p := SecondOrderPairObjects.ordered_unique_l hℳ hPair' hPair
    exact hqp ▸ hq

/-- 初值 X 与相对构造基集可以不同；矩阵的实际四参数必须在母集内。 -/
theorem member_l {X D W α C C₁ C₂ f : type_l hℳ}
    (hD : PowerlessFunctionHistoryAgreement.functional_l hℳ D)
    (hα : Ordinal α) (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ α)
    (hf : PowerlessHierarchyLightHistory.history_l hℳ X D α W f)
    (hTrans : ∀ x, mem_l hℳ x C → ∀ y, mem_l hℳ y x → mem_l hℳ y C)
    (hDef₁ : SecondOrderMemberDef.spec_l hℳ C C₁)
    (hDef₂ : SecondOrderMemberDef.spec_l hℳ C₁ C₂)
    (hXC : mem_l hℳ X C) (hDC : mem_l hℳ D C)
    (hWC : mem_l hℳ W C) (hαC : mem_l hℳ α C)
    (hCover : ∀ β, mem_l hℳ β α → ∃ g, mem_l hℳ g C ∧
      PowerlessHierarchyLightHistory.history_l hℳ X D β W g) : mem_l hℳ f C₂ := by
  let η : Env 𝒱 [] [.set, .set, .set, .set] :=
    Env.empty |>.pushFree X |>.pushFree D |>.pushFree W |>.pushFree α
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] :=
    body_m (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there .here)))) (.fvar (.there .here))
      (.fvar (.there (.there .here))) (.fvar .here)
  have hFormula (g : type_l hℳ) : φ.satisfies (η.pushFree g) ↔
      ∃ β, mem_l hℳ β α ∧ PowerlessHierarchyLightHistory.history_l hℳ X D β W g :=
    body_reading_l hℳ (η.pushFree g) _ _ _ _ _
  obtain ⟨H, hH⟩ := (SecondOrderSeparationAxiom.schema_l hℳ φ η).mp
    (SecondOrderSeparationAxiom.models_l hℳ φ η) C
  have hRead (g : type_l hℳ) : mem_l hℳ g H ↔ mem_l hℳ g C ∧
      ∃ β, mem_l hℳ β α ∧ PowerlessHierarchyLightHistory.history_l hℳ X D β W g :=
    (hH g).trans (and_congr Iff.rfl (hFormula g))
  have hHC₁ : mem_l hℳ H C₁ := by
    apply SecondOrderMemberDefBoundedSlice.member_l (φ := φ) hℳ hDef₁ hTrans
      (body_delta_l _ _ _ _ _) η
    · intro s v
      cases s
      cases v with
      | here => exact hαC
      | there v => cases v with
        | here => exact hWC
        | there v => cases v with
          | here => exact hDC
          | there v => cases v with
            | here => exact hXC
            | there v => nomatch v
    · exact hH
  have hTrans₁ := SecondOrderMemberDefProperties.transitive_l hℳ hDef₁
    (fun x y hx hy => hTrans x hx y hy)
  exact SecondOrderMemberDefBasicClosure.union_l hℳ hDef₂ hHC₁
    (fun x hx y hy => hTrans₁ x y hx hy) (union_l hℳ hD hα hLimit hf hRead hCover)

#print axioms union_l
#print axioms member_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFunctionHistoryLimitBound
