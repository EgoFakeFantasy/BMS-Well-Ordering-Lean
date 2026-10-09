import BMSConstructibleBridge.SecondOrderComparisonNativeConfiguration
import BMSConstructibleBridge.SecondOrderEnumerationAmbientWellOrder
import BMSConstructibleBridge.SecondOrderMemberEnumeration
import BMSConstructibleBridge.SecondOrderComparisonDecodePreservation

/-! # 比较递归的实际共同载体、枚举与初始良序

取基底与层函数陪域之并的并，得到共同成员载体。陪域无需是精确值域，
也不取其幂集。基底非空保证共同载体非空，实际成员枚举给出 ω 满射；
初始序在全部环境子集上良序。所有对象先于候选历史固定。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonStaticSupport

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderComparisonNativeRow (parameters_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "v" => SecondOrderQuotient.mk_l hℳ

structure support_l (K : source_coding_l hℳ) (B r C f P₀ : type_l hℳ) : Prop where
  base : subset_l (ℳ := 𝒱) B C
  layers : ∀ X, mem_l hℳ X r → subset_l (ℳ := 𝒱) X C
  enumeration : map_l (ℳ := 𝒱) f K.omega C
  onto : ∀ x, mem_l hℳ x C → ∃ i, mem_l hℳ i K.omega ∧ value_l (ℳ := 𝒱) f i x
  initialOrder : wellOrder_l (ℳ := 𝒱) B P₀
  initialBound : ∀ p, mem_l hℳ p P₀ → ∃ x y,
    mem_l hℳ x B ∧ mem_l hℳ y B ∧ SecondOrderPairObjects.ordered_l hℳ x y p

private theorem enumeration_exists_l (K : source_coding_l hℳ) (X : type_l hℳ)
    (hX : ∃ x, mem_l hℳ x X) : ∃ f : type_l hℳ,
      map_l (ℳ := 𝒱) f K.omega X ∧
      ∀ x, mem_l hℳ x X → ∃ i, mem_l hℳ i K.omega ∧ value_l (ℳ := 𝒱) f i x := by
  obtain ⟨x, hx⟩ := hX
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ X
  obtain ⟨a, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
  obtain ⟨n, hn, _⟩ := (SecondOrderQuotient.mem_iff_l hℳ a A).mp hx
  obtain ⟨f, hf, _, hOnto⟩ := SecondOrderMemberEnumeration.exists_l K A n hn
  exact ⟨f, hf, hOnto⟩

theorem exists_l (K : source_coding_l hℳ) (B r : type_l hℳ)
    (hB : ∃ b, mem_l hℳ b B) : ∃ C f P₀, support_l K B r C f P₀ := by
  have hUnion := SecondOrderUnion.models_l hℳ
  change ∀ a : type_l hℳ, ∃ c, ∀ x, mem_l hℳ x c ↔
    ∃ y, mem_l hℳ y a ∧ mem_l hℳ x y at hUnion
  obtain ⟨U, hU⟩ := hUnion r
  obtain ⟨S, hS⟩ := SecondOrderPairObjects.pair_exists_l hℳ B U
  obtain ⟨C, hC⟩ := hUnion S
  have hBC : subset_l (ℳ := 𝒱) B C := fun x hx =>
    (hC x).mpr ⟨B, (hS B).mpr (Or.inl rfl), hx⟩
  have hLayers : ∀ X, mem_l hℳ X r → subset_l (ℳ := 𝒱) X C := by
    intro X hX x hx
    exact (hC x).mpr ⟨U, (hS U).mpr (Or.inr rfl), (hU x).mpr ⟨X, hX, hx⟩⟩
  have hNonempty : ∃ x, mem_l hℳ x C := hB.imp (fun x hx => hBC x hx)
  obtain ⟨f, hf, hOnto⟩ := enumeration_exists_l K C hNonempty
  obtain ⟨g, hg, hBaseOnto⟩ := enumeration_exists_l K B hB
  obtain ⟨P, hOrder⟩ := SecondOrderEnumerationAmbientWellOrder.exists_l
    (hℳ := hℳ) (ω := K.omega) (G := g) (X := B) K.omega_spec hg hBaseOnto
  obtain ⟨W, hW, _⟩ := SecondOrderComparisonReal.exists_unique_l K g P
  obtain ⟨P₀, hP₀⟩ := SecondOrderComparisonDecode.exists_l K B g W
  have hInitial := SecondOrderComparisonDecodePreservation.wellOrder_l K hg hBaseOnto hW hP₀
    (fun _ h => h) hOrder
  refine ⟨C, f, P₀, hBC, hLayers, hf, hOnto, hInitial, ?_⟩
  intro p hp
  obtain ⟨x, y, hxy, hPair⟩ := (hP₀ p).mp hp
  exact ⟨x, y, hxy.1, hxy.2.1, hPair⟩

/-- 固定已给的基底序；改变层次陪域只需重新取共同载体及其枚举。 -/
theorem with_initial_l (K : source_coding_l hℳ) (B r P₀ : type_l hℳ)
    (hB : ∃ b, mem_l hℳ b B) (hOrder : wellOrder_l (ℳ := 𝒱) B P₀)
    (hBound : ∀ p, mem_l hℳ p P₀ → ∃ x y,
      mem_l hℳ x B ∧ mem_l hℳ y B ∧ SecondOrderPairObjects.ordered_l hℳ x y p) :
    ∃ C f, support_l K B r C f P₀ := by
  obtain ⟨C, f, _, h⟩ := exists_l K B r hB
  exact ⟨C, f, { h with initialOrder := hOrder, initialBound := hBound }⟩

/-- 将实际支撑对象填入同一个配置，不在历史量词之内重新选参数。 -/
theorem configuration_exists_l (K : source_coding_l hℳ)
    {t₁ t₂ t₃ Pair Valid : type_l hℳ}
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (A : SecondOrderGraph.code_l ℳ)
    (hα : SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) (v A))
    {B F r : type_l hℳ} (hF : PowerlessRelativeHierarchySemantics.history_l hℳ B (v A) F r)
    (hB : ∃ b, mem_l hℳ b B) : ∃ Q D R p,
      SecondOrderComparisonNativeConfiguration.configuration_l K p A B F r Q D R ∧
        support_l K B r (v p.C) (v p.f) (v p.P₀) := by
  obtain ⟨C, f, P₀, hSupport⟩ := exists_l K B r hB
  obtain ⟨Q, D, R, p, hConfig, hP₀, hf, hC, _, _⟩ :=
    SecondOrderComparisonNativeConfiguration.exists_l K hCoding A hα hF P₀ f C
  exact ⟨Q, D, R, p, hConfig, by simpa only [hP₀, hf, hC] using hSupport⟩

#print axioms exists_l
#print axioms with_initial_l
#print axioms configuration_exists_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonStaticSupport
