import BMSConstructibleBridge.PowerlessCanonicalCodedEdgeSyntax
import BMSConstructibleBridge.PowerlessRelativeClassCanonicalCodedCoverage
import BMSConstructibleBridge.PowerlessRelativeClassCanonicalLevelReading
import BMSConstructibleBridge.SecondOrderCanonicalCodingAgreement
import BMSConstructibleBridge.SecondOrderCanonicalClassOrder

/-! # 类内完整覆盖比较与原全局规范序一致

原 Z₂、纯隶属 ℒ。同一内部编码下不同局部静态包只按已证规格认同；
合法性图保持读值认同，不要求对象相等。原规范层初段性把右端的
全部前驱压入实际 Class 覆盖层，得到双向比较读数。原参考历史、
Class 比较图和覆盖包均由已验证的构造取得，不作为额外输入。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalEdgeReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ z, mem_l hℳ z B → ∀ t, mem_l hℳ t z → mem_l hℳ t B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => structure_l hℳ B hBase
local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "M" => type_l hℳ B

variable {t₁₀ t₂₀ t₃₀ Pair₀ Valid₀ : SecondOrderQuotient.type_l hℳ}

private abbrev zero_l (K : source_coding_l hℳ) := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val

/-- 原完整 Class 规范覆盖中的选定比较值，在固定全局编码下仍是原规范层。 -/
theorem selected_l (K : source_coding_l hℳ)
    (B₀ ω x P₀ a X A U D f e t₁ t₂ t₃ t₄ Pair N Valid V Q G g R P : M)
    (hB₀ : B₀.val = B) (hω : ω.val = K.omega)
    (hPoint : PowerlessCanonicalCodedCoverageSyntax.point_l (𝒩 := 𝒩₀)
      B₀ ω x P₀ a X A U D f e t₁ t₂ t₃ t₄ Pair N Valid V Q G g R P)
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁₀ t₂₀ t₃₀ Pair₀ Valid₀)
    (hB : ∃ b, mem_l hℳ b B) (hSeed : wellOrder_l (ℳ := 𝒱) B P₀.val)
    (hBound : ∀ p, mem_l hℳ p P₀.val → ∃ z t,
      mem_l hℳ z B ∧ mem_l hℳ t B ∧ SecondOrderPairObjects.ordered_l hℳ z t p) :
    SecondOrderCanonicalLevelSyntax.level_l K.omega (zero_l K)
      t₁₀ t₂₀ t₃₀ Pair₀ Valid₀ B P₀.val a.val X.val P.val := by
  have hRead := PowerlessRelativeClassCanonicalLevelReading.reading_l (hBase := hBase)
    K B₀ ω x a X A U D f e t₁ t₂ t₃ t₄ Pair N Valid V Q G P₀ g R
    hB₀ hω hPoint.1 hB hSeed hBound hPoint.2.1 hPoint.2.2.1
  have hFX := (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f a X).mp hPoint.1.2.1
  have hGP := (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) g a P).mp hPoint.2.2.2
  have hLevel := (hRead a.val X.val P.val hFX).mp hGP
  obtain ⟨he, ht₁, ht₂, ht₃, _hN, hPairMap, hPair, hValid⟩ :=
    PowerlessRelativeClassStaticCodingReading.reading_l (hBase := hBase) K hω hPoint.1.2.2.2.2.2.1
  obtain ⟨V₀, hV₀, _⟩ := SecondOrderTriangularFormulaSyntax.exists_l hℳ
  have hCoding' : SecondOrderComparisonStageTotal.coding_l K
      t₁.val t₂.val t₃.val Pair.val Valid.val :=
    ⟨ht₁, ht₂, ht₃, hPairMap, hPair, V₀, hV₀, hValid V₀ hV₀⟩
  have he' : e.val = zero_l K := he
  rw [hω, he'] at hLevel
  exact (SecondOrderCanonicalCodingAgreement.level_l K hCoding' hCoding).mp hLevel

theorem edge_l (K : source_coding_l hℳ) (ω P₀ x y : M)
    (hω : ω.val = K.omega)
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁₀ t₂₀ t₃₀ Pair₀ Valid₀)
    (hB : ∃ b, mem_l hℳ b B) (hSeed : wellOrder_l (ℳ := 𝒱) B P₀.val)
    (hBound : ∀ p, mem_l hℳ p P₀.val → ∃ z t,
      mem_l hℳ z B ∧ mem_l hℳ t B ∧ SecondOrderPairObjects.ordered_l hℳ z t p) :
    PowerlessCanonicalCodedEdgeSyntax.edge_l (𝒩 := 𝒩₀)
      ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ ω P₀ x y ↔
    SecondOrderCanonicalClassOrder.edge_l K.omega (zero_l K)
      t₁₀ t₂₀ t₃₀ Pair₀ Valid₀ B P₀.val x.val y.val := by
  let B₀ : M := ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩
  constructor
  · rintro ⟨a, X, A, U, D, f, e, t₁, t₂, t₃, t₄, Pair, N, Valid, V, Q, G,
      g, R, P, hPoint, hx, hxy⟩
    have hLevel := selected_l K B₀ ω y P₀ a X A U D f e t₁ t₂ t₃ t₄
      Pair N Valid V Q G g R P rfl hω hPoint hCoding hB hSeed hBound
    exact ⟨a.val, X.val, P.val, hLevel, hx, hPoint.1.2.2.1,
      (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) P x y).mp hxy⟩
  · intro hxy
    obtain ⟨a, X, A, U, D, f, e, t₁, t₂, t₃, t₄, Pair, N, Valid, V, Q, G,
      g, R, P, hPoint⟩ := PowerlessRelativeClassCanonicalCodedCoverage.exists_l (hBase := hBase)
        K ω y P₀ (hω.symm ▸ K.omega_spec) hB hSeed hBound
    have hLevel := selected_l K B₀ ω y P₀ a X A U D f e t₁ t₂ t₃ t₄
      Pair N Valid V Q G g R P rfl hω hPoint hCoding hB hSeed hBound
    have hyX : mem_l hℳ y.val X.val := hPoint.1.2.2.1
    have hxX := SecondOrderCanonicalClassOrder.initial_l K hCoding hLevel hyX hxy
    have hValue := (SecondOrderCanonicalClassOrder.restrict_l K hCoding hLevel hxX hyX).mp hxy
    exact ⟨a, X, A, U, D, f, e, t₁, t₂, t₃, t₄, Pair, N, Valid, V, Q, G,
      g, R, P, hPoint, hxX,
      (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) P x y).mpr hValue⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalEdgeReading
