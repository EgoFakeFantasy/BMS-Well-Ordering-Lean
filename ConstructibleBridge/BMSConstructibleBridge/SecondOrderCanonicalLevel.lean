import BMSConstructibleBridge.SecondOrderCanonicalLevelSyntax

/-! # 任意实际层的规范序：存在、唯一与跨历史初段

固定一次基底序及编码包，实际内部递归构造每份证书；不同阶段界的
证书由共同阶段归纳比较。这里只在 Prop 中使用存在见证，不选取类函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalLevel

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderCanonicalLevelSyntax (level_l history_l)
open SecondOrderComparisonHistoryAgreementStep (read_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "v" => SecondOrderQuotient.mk_l hℳ
private abbrev zero_l (K : source_coding_l hℳ) := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val

theorem unique_l (K : source_coding_l hℳ)
    {t₁ t₂ t₃ Pair Valid B P₀ a X P Y Q : type_l hℳ}
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (hP : level_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ a X P)
    (hQ : level_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ a Y Q) : X = Y ∧ P = Q := by
  obtain ⟨A, F, r, I, J, T, G, q, h, hRead⟩ := hP
  obtain ⟨A', F', r', I', J', T', G', q', h', hRead'⟩ := hQ
  have ha : mem_l hℳ a A := by
    obtain ⟨i, hia, _⟩ := hRead
    exact (SecondOrderFunctionLaws.value_mem_l hℳ h.configuration.indexMap hia).2
  have ha' : mem_l hℳ a A' := by
    obtain ⟨i, hia, _⟩ := hRead'
    exact (SecondOrderFunctionLaws.value_mem_l hℳ h'.configuration.indexMap hia).2
  exact ⟨SecondOrderComparisonHistoryAgreementStep.layer_equal_l h.configuration h'.configuration hRead hRead',
    SecondOrderComparisonHistoryAgreement.agree_l K h.configuration h'.configuration
      h.comparisonMap h'.comparisonMap hCoding h.canonical h'.canonical a ⟨ha, ha'⟩ X P Y Q ⟨hRead, hRead'⟩⟩

theorem order_l {ω e t₁ t₂ t₃ Pair Valid B P₀ a X P : type_l hℳ}
    (hP : level_l ω e t₁ t₂ t₃ Pair Valid B P₀ a X P) : wellOrder_l (ℳ := 𝒱) X P := by
  obtain ⟨_, _, _, _, _, _, _, _, h, i, hia, hiX, hiP⟩ := hP
  obtain ⟨hi, ha⟩ := SecondOrderFunctionLaws.value_mem_l hℳ h.configuration.indexMap hia
  exact (h.invariant a ha i X P ⟨⟨hi, hiX, hiP⟩, hia⟩).1

/-- 比较层仍是原相对层次的同一层，并非另造一个同名载体。 -/
theorem hierarchy_l {ω e t₁ t₂ t₃ Pair Valid B P₀ a X P : type_l hℳ}
    (hP : level_l ω e t₁ t₂ t₃ Pair Valid B P₀ a X P) :
    PowerlessRelativeHierarchySemantics.level_l hℳ B a X := by
  obtain ⟨A, F, r, _, _, _, _, _, h, i, hia, hiX, _⟩ := hP
  obtain ⟨b, hib, hbX⟩ := (h.configuration.layerRead i X).mp hiX
  have hba := SecondOrderFunctionLaws.value_unique_l hℳ h.configuration.indexMap hib hia
  exact ⟨A, F, r, h.configuration.ordinal,
    (SecondOrderFunctionLaws.value_mem_l hℳ h.configuration.indexMap hia).2,
    h.configuration.hierarchy, hba ▸ hbX⟩

theorem extension_l (K : source_coding_l hℳ)
    {t₁ t₂ t₃ Pair Valid B P₀ a b X P Y Q : type_l hℳ}
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (hab : mem_l hℳ a b)
    (hP : level_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ a X P)
    (hQ : level_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ b Y Q) :
    SecondOrderWellOrderCoherentUnion.extension_l (ℳ₀ := 𝒱) X P Y Q := by
  obtain ⟨A, F, r, I, J, T, G, q, h, i, hib, hiY, hiQ⟩ := hQ
  obtain ⟨hi, hb⟩ := SecondOrderFunctionLaws.value_mem_l hℳ h.configuration.indexMap hib
  have ha := h.configuration.ordinal.transitive b hb a hab
  obtain ⟨j, hj, hja⟩ := h.configuration.indexOnto a ha
  obtain ⟨Z, ⟨_, hjZ⟩, _⟩ := h.configuration.layerMap.2 j hj
  obtain ⟨R, ⟨_, hjR⟩, _⟩ := h.comparisonMap.2 j (h.configuration.indexSubset j hj)
  have hR : level_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ a Z R :=
    ⟨A, F, r, I, J, T, G, q, h, j, hja, hjZ, hjR⟩
  obtain ⟨hXZ, hPR⟩ := unique_l K hCoding hP hR
  subst Z
  subst R
  exact (h.invariant b hb i Y Q ⟨⟨hi, hiY, hiQ⟩, hib⟩).2 j X P ⟨⟨hj, hjZ, hjR⟩, a, hja, hab⟩

theorem history_exists_l (K : source_coding_l hℳ)
    {t₁ t₂ t₃ Pair Valid B P₀ A F r : type_l hℳ}
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (hB : ∃ b, mem_l hℳ b B)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hOrder : wellOrder_l (ℳ := 𝒱) B P₀)
    (hBound : ∀ p, mem_l hℳ p P₀ → ∃ x y,
      mem_l hℳ x B ∧ mem_l hℳ y B ∧ SecondOrderPairObjects.ordered_l hℳ x y p)
    (hA : SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) A)
    (hF : PowerlessRelativeHierarchySemantics.history_l hℳ B A F r) :
    ∃ I J T G q, history_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ A F r I J T G q := by
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ A
  obtain ⟨C, f, hSupport⟩ := SecondOrderComparisonStaticSupport.with_initial_l K B r P₀ hB hOrder hBound
  obtain ⟨Root, Index, Prec, p, hConfig, hP₀, hf, hC, hPair, hValid⟩ :=
    SecondOrderComparisonNativeConfiguration.exists_l K hCoding A hA hF P₀ f C
  have hSupport' : SecondOrderComparisonStaticSupport.support_l K B r (v p.C) (v p.f) (v p.P₀) := by
    simpa only [hP₀, hf, hC] using hSupport
  obtain ⟨_, _, q, G, _, _, _, hG, hInvariant, _, _, _, hCanonical⟩ :=
    SecondOrderComparisonHistoryInvariant.exists_l K p hConfig hSupport' hBase
  have ht₁ := hConfig.coding.one.trans hCoding.one.symm
  have ht₂ := hConfig.coding.two.trans hCoding.two.symm
  have ht₃ := hConfig.coding.three.trans hCoding.three.symm
  refine ⟨v p.I, v p.J, v p.T, G, q,
    SecondOrderComparisonIndexedConfiguration.of_native_l hConfig, hG.1, ?_, hInvariant⟩
  simpa only [hP₀, hPair, hValid, ht₁, ht₂, ht₃] using hCanonical

/-- 每个已有层都有唯一规范序；不把规范证书的存在留作假设。 -/
theorem exists_unique_l (K : source_coding_l hℳ)
    {t₁ t₂ t₃ Pair Valid B P₀ a X : type_l hℳ}
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (hB : ∃ b, mem_l hℳ b B)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hOrder : wellOrder_l (ℳ := 𝒱) B P₀)
    (hBound : ∀ p, mem_l hℳ p P₀ → ∃ x y,
      mem_l hℳ x B ∧ mem_l hℳ y B ∧ SecondOrderPairObjects.ordered_l hℳ x y p)
    (hX : PowerlessRelativeHierarchySemantics.level_l hℳ B a X) :
    ∃! P, level_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ a X P := by
  obtain ⟨A, F, r, hA, ha, hF, haX⟩ := hX
  obtain ⟨I, J, T, G, q, h⟩ := history_exists_l K hCoding hB hBase hOrder hBound hA hF
  obtain ⟨i, hi, hia⟩ := h.configuration.indexOnto a ha
  obtain ⟨P, ⟨_, hiP⟩, _⟩ := h.comparisonMap.2 i (h.configuration.indexSubset i hi)
  have hP : level_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ a X P :=
    ⟨A, F, r, I, J, T, G, q, h, i, hia, (h.configuration.layerRead i X).mpr ⟨a, hia, haX⟩, hiP⟩
  exact ⟨P, hP, fun Q hQ => (unique_l K hCoding hQ hP).2⟩

#print axioms unique_l
#print axioms extension_l
#print axioms exists_unique_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalLevel
