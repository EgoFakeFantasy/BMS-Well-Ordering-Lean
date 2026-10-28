import BMSConstructibleBridge.PowerlessRelativeClassCanonicalStepReading

/-! # 真正 Class 规范后继向原商的反向读数

背景为原 Z₂。母序的 raw 良序证书显式保留；不能一般地把 Class
良序扩大到所有 raw 子集。给定规范指标与原构造的指标通过唯一性
相等，给定精确行图再与实际环境良序图相等，故保留同一全部图对象。
这消去任意候选的 Class 最小元量词限制，而非假定一般良序绝对。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalStepAmbient

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => structure_l hℳ B hBase
local notation "M" => type_l hℳ B

theorem queryRead_l {ω A S I R J Q : M}
    (h : SecondOrderCanonicalOrderSyntax.queryRead_l (ℳ₀ := 𝒩₀) ω A S I R J Q) :
    SecondOrderCanonicalOrderSyntax.queryRead_l (ℳ₀ := 𝒱)
      ω.val A.val S.val I.val R.val J.val Q.val := by
  have hRead (t x : M) : value_l (ℳ := 𝒱) Q.val t.val x.val ↔
      mem_l hℳ t.val J.val ∧ mem_l hℳ x.val A.val ∧
        PowerlessRelativeClassSatisfactionAllSlots.query_l (ℳ₀ := 𝒱)
          ω.val A.val S.val I.val R.val t.val x.val :=
    (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) Q t x).symm.trans
      ((h t x).trans (and_congr Iff.rfl (and_congr Iff.rfl
        (PowerlessRelativeClassCanonicalStepReading.query_l ω A S I R t x))))
  intro t x
  constructor
  · intro hValue
    have hCoordinates := PowerlessRelativeClassValueCoordinates.value_l hBase Q hValue
    exact (hRead ⟨t, hCoordinates.1⟩ ⟨x, hCoordinates.2⟩).mp hValue
  · rintro ⟨ht, hx, hBody⟩
    let t₀ : M := ⟨t, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase J.property ht⟩
    let x₀ : M := ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase A.property hx⟩
    exact (hRead t₀ x₀).mpr ⟨ht, hx, hBody⟩

theorem graph_l {I U A Q Y L : M}
    (h : PowerlessRelativeClassRowOrderCanonical.graph_l (ℳ₀ := 𝒩₀) I U A Q Y L) :
    PowerlessRelativeClassRowOrderCanonical.graph_l (ℳ₀ := 𝒱)
      I.val U.val A.val Q.val Y.val L.val := by
  intro p
  constructor
  · intro hp
    let p₀ : M := ⟨p, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase L.property hp⟩
    obtain ⟨x, y, hx, hy, hxy, hBody⟩ := (h p₀).mp hp
    exact ⟨x.val, y.val, hx, hy,
      (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) x y p₀).mp hxy,
      (PowerlessRelativeClassCanonicalStepReading.comparison_l I U A Q x y).mp hBody⟩
  · rintro ⟨x, y, hx, hy, hxy, hBody⟩
    let x₀ : M := ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Y.property hx⟩
    let y₀ : M := ⟨y, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Y.property hy⟩
    let p₀ : M := ⟨p, PowerlessRelativeClassPair.ordered_l hℳ hBase x₀.property y₀.property hxy⟩
    exact (h p₀).mpr ⟨x₀, y₀, hx, hy,
      (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) x₀ y₀ p₀).mpr hxy,
      (PowerlessRelativeClassCanonicalStepReading.comparison_l I U A Q x₀ y₀).mpr hBody⟩

theorem extension_l {A D P L E : M}
    (h : SecondOrderWellOrderEndExtensionUnique.graph_l (ℳ₀ := 𝒩₀) A D P L E) :
    SecondOrderWellOrderEndExtensionUnique.graph_l (ℳ₀ := 𝒱)
      A.val D.val P.val L.val E.val := by
  have hBody (x y : M) : SecondOrderWellOrderEndExtension.body_l (ℳ₀ := 𝒩₀) A P L x y ↔
      SecondOrderWellOrderEndExtension.body_l (ℳ₀ := 𝒱) A.val P.val L.val x.val y.val :=
    or_congr
      (and_congr Iff.rfl (and_congr Iff.rfl
        (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) P x y)))
      (or_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
        (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) L x y))))
  intro p
  constructor
  · intro hp
    let p₀ : M := ⟨p, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase E.property hp⟩
    obtain ⟨x, y, hx, hy, hStep, hxy⟩ := (h p₀).mp hp
    exact ⟨x.val, y.val, hx, hy, (hBody x y).mp hStep,
      (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) x y p₀).mp hxy⟩
  · rintro ⟨x, y, hx, hy, hStep, hxy⟩
    let x₀ : M := ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase D.property hx⟩
    let y₀ : M := ⟨y, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase D.property hy⟩
    let p₀ : M := ⟨p, PowerlessRelativeClassPair.ordered_l hℳ hBase x₀.property y₀.property hxy⟩
    exact (h p₀).mpr ⟨x₀, y₀, hx, hy, (hBody x₀ y₀).mpr hStep,
      (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) x₀ y₀ p₀).mpr hxy⟩

/-- 规范性重建环境良序，不使用任意 Class 良序的无条件反向传输。 -/
theorem candidate_l {ω A P R D L : M} (hΩ : omega_l (ℳ := 𝒩₀) ω)
    (hP : wellOrder_l (ℳ := 𝒱) A.val P.val)
    (h : SecondOrderCanonicalOrderSyntax.candidate_l (ℳ₀ := 𝒩₀) ω A P R D L) :
    PowerlessRelativeClassCanonicalOrderStep.candidate_l (hBase := hBase) ω A P R D L := by
  obtain ⟨S, I, J, U, Q, Y, hIndex, hRead, hRows, hGraph, hSubset, _hOrderClass⟩ := h
  obtain ⟨S₁, I₁, J₁, U₁, hIndex₁, hU₁⟩ :=
    PowerlessRelativeClassSatisfactionIndexCanonical.exists_l hΩ hP
  have hU : wellOrder_l (ℳ := 𝒱) J.val U.val := by
    obtain ⟨rfl, rfl, rfl, rfl⟩ := PowerlessRelativeClassSatisfactionIndexCanonical.unique_l hIndex hIndex₁
    exact hU₁
  have hGraphRaw := graph_l hGraph
  obtain ⟨Y₁, L₁, hRows₁, hGraph₁, hOrder₁⟩ :=
    PowerlessRelativeClassRowOrderCanonical.exists_l J A Q U hU
  have hOrder : wellOrder_l (ℳ := 𝒱) Y.val L.val := by
    have hY : Y = Y₁ := PowerlessRelativeClassRowOrderCanonical.family_unique_l hRows hRows₁
    subst Y₁
    have hL : L.val = L₁.val := PowerlessRelativeClassRowOrderCanonical.graph_unique_l hGraphRaw hGraph₁
    exact hL.symm ▸ hOrder₁
  refine ⟨S, I, J, U, Q, Y, hIndex, queryRead_l hRead, hRows, hGraphRaw, ?_, hOrder⟩
  intro x hx
  exact hSubset ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase D.property hx⟩ hx

theorem step_l {ω A P R D E : M} (hΩ : omega_l (ℳ := 𝒩₀) ω)
    (hP : wellOrder_l (ℳ := 𝒱) A.val P.val)
    (h : SecondOrderCanonicalOrderSyntax.step_l (ℳ₀ := 𝒩₀) ω A P R D E) :
    PowerlessRelativeClassCanonicalOrderStep.step_l (hBase := hBase) ω A P R D E := by
  obtain ⟨L, hCandidate, hGraph⟩ := h
  exact ⟨L, candidate_l hΩ hP hCandidate, extension_l hGraph⟩

theorem uniform_l (K : source_coding_l hℳ) {ω A P e t₁ t₂ t₃ Pair Valid D E : M}
    (hω : ω.val = K.omega) (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hPairMap : map_l (ℳ := 𝒱) Pair.val K.omega K.omega)
    (hPair : PowerlessBMSQuotientPairingBounds.spec_l K Pair.val)
    (hP : wellOrder_l (ℳ := 𝒱) A.val P.val)
    (h : SecondOrderCanonicalOrderUniform.step_l (ℳ₀ := 𝒩₀) ω A P e t₁ t₂ t₃ Pair Valid D E) :
    SecondOrderCanonicalOrderUniform.step_l (ℳ₀ := 𝒱)
      ω.val A.val P.val e.val t₁.val t₂.val t₃.val Pair.val Valid.val D.val E.val := by
  have hΩ : omega_l (ℳ := 𝒩₀) ω :=
    (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mpr (hω.symm ▸ K.omega_spec)
  obtain ⟨R, hR, hStep⟩ := h
  exact ⟨R.val, PowerlessRelativeClassSatisfactionAbsolute.spec_l K hω he hPairMap hPair hR,
    SecondOrderCanonicalOrderSyntax.step_ambient_l hΩ (step_l hΩ hP hStep)⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalStepAmbient
