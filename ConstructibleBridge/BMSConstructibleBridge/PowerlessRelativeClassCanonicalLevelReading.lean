import BMSConstructibleBridge.PowerlessRelativeClassCodedHistoryReading
import BMSConstructibleBridge.PowerlessRelativeClassCanonicalHistoryAgreement
import BMSConstructibleBridge.PowerlessCanonicalOrderClassHistory

/-! # 完整类内检查器与规范层的同图认同

原 Z₂、纯隶属 ℒ。类内完整包给出同一原层图；原递归实际构造参考
比较历史，内部认同消去参考历史前提，给定的 g 保持不变。类内
无枚举规范方程及干净函数规格决定原规范层证书，不假定整张
计数式层次 AST 绝对，也不要求参考数字编号图属于 Class。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalLevelReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => structure_l hℳ B hBase
local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "M" => type_l hℳ B

theorem reading_l (K : source_coding_l hℳ)
    (B₀ ω x a y A U D f e t₁ t₂ t₃ t₄ Pair N Valid V Q G P₀ g R : M)
    (hB₀ : B₀.val = B) (hω : ω.val = K.omega)
    (hPoint : PowerlessCodedHistoryCoverageSyntax.point_l (𝒩 := 𝒩₀)
      B₀ ω x a y A U D f e t₁ t₂ t₃ t₄ Pair N Valid V Q G)
    (hB : ∃ b, mem_l hℳ b B)
    (hSeed : wellOrder_l (ℳ := 𝒱) B P₀.val)
    (hBound : ∀ p, mem_l hℳ p P₀.val → ∃ z t,
      mem_l hℳ z B ∧ mem_l hℳ t B ∧ SecondOrderPairObjects.ordered_l hℳ z t p)
    (hg : map_l (ℳ := 𝒩₀) g A R)
    (hEq : PowerlessCanonicalOrderEquations.holds_l (𝒩 := 𝒩₀)
      ω e t₁ t₂ t₃ Pair Valid B₀ P₀ f g) :
    ∀ b X P, value_l (ℳ := 𝒱) f.val b X →
      (value_l (ℳ := 𝒱) g.val b P ↔ SecondOrderCanonicalLevelSyntax.level_l
        ω.val e.val t₁.val t₂.val t₃.val Pair.val Valid.val B P₀.val b X P) := by
  have hStatic := hPoint.2.2.2.2.2.1
  have hRaw := PowerlessRelativeClassCodedHistoryReading.point_l
    K B₀ ω x a y A U D f e t₁ t₂ t₃ t₄ Pair N Valid V Q G hω hPoint
  have hHistory := PowerlessRawCodedHistoryReading.history_l K hω hRaw
  rw [hB₀] at hHistory
  have hA := hRaw.2.2.2.2.2.2.2.2.2.1
  obtain ⟨he, ht₁, ht₂, ht₃, _hN, hPairMap, hPair, hValid⟩ :=
    PowerlessRelativeClassStaticCodingReading.reading_l K hω hStatic
  have he' : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val := he
  obtain ⟨V₀, hV₀, _⟩ := SecondOrderTriangularFormulaSyntax.exists_l hℳ
  have hCoding : SecondOrderComparisonStageTotal.coding_l K
      t₁.val t₂.val t₃.val Pair.val Valid.val :=
    ⟨ht₁, ht₂, ht₃, hPairMap, hPair, V₀, hV₀, hValid V₀ hV₀⟩
  obtain ⟨I, J, T, H, q, hReference⟩ := SecondOrderCanonicalLevel.history_exists_l
    K hCoding hB hBase hSeed hBound hA hHistory
  obtain ⟨g₀, hg₀, hRead₀, hLevel, _hCanonical⟩ :=
    PowerlessCanonicalOrderOrdinalHistory.exists_l K hCoding hReference
  have hEq₀ := PowerlessCanonicalOrderClassHistory.equations_l K hReference hRead₀ hBound
  have hRawEq : PowerlessCanonicalOrderEquations.holds_l (𝒩 := 𝒱)
      ω.val e.val t₁.val t₂.val t₃.val Pair.val Valid.val B₀.val P₀.val f.val g₀ := by
    rw [hω, he', hB₀]
    exact hEq₀
  have hOrder₀ b X P (hX : value_l (ℳ := 𝒱) f.val b X)
      (hP : value_l (ℳ := 𝒱) g₀ b P) : wellOrder_l (ℳ := 𝒱) X P :=
    SecondOrderCanonicalLevel.order_l ((hLevel b X P hX).mp hP)
  have hSame := PowerlessRelativeClassCanonicalHistoryAgreement.unique_l
    (hBase := hBase) (r := U.val) (q := R.val) (q₀ := q) (g₀ := g₀)
    K ω e t₁ t₂ t₃ Pair N Valid B₀ P₀ f g hω hStatic hA hHistory.1
      ((PowerlessRelativeClassFunctionAbsolute.map_l g A R).mp hg) hg₀ hEq hRawEq hOrder₀
  intro b X P hX
  rw [hSame, hω, he']
  exact hLevel b X P hX

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalLevelReading
