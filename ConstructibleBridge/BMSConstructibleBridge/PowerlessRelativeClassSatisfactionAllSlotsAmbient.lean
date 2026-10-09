import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionAllSlots
import BMSConstructibleBridge.PowerlessRelativeClassSequenceWellOrderAmbient

/-! # 全内部槽位 Sat 子集族的环境良序

表示空间 ω × (ω × Seq(A)) 的同一积图在环境中良序。
类内最小表示仅用于构造单射截面；环境单射拉回工具独立处理
任意环境子集。结论的良序量词不相对化，行族规格保留类内精确读数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSatisfactionAllSlotsAmbient

open Logic FirstOrder ThirdOrderSemantics
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassSatisfactionAllSlots (query_m query_l query_delta_l query_formula_l read_l family_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
    ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

local notation "𝒩" => structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l {ω A P : type_l hℳ B}
    (hω : omega_l (ℳ := 𝒩) ω) (hP : wellOrder_l (ℳ := 𝒱) A.val P.val)
    (R : type_l hℳ B) :
    ∃ S I Y L : type_l hℳ B, PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒩) ω A S ∧
      (∀ p, SecondOrderQuotient.mem_l hℳ p.val I.val ↔ ∃ c f : type_l hℳ B,
        SecondOrderQuotient.mem_l hℳ c.val ω.val ∧
        SecondOrderQuotient.mem_l hℳ f.val S.val ∧ ordered_l (ℳ := 𝒩) c f p) ∧
      family_l (ℳ₀ := 𝒩) ω A S I R Y ∧ wellOrder_l (ℳ := 𝒱) Y.val L.val := by
  obtain ⟨S, T, hS, hT, _⟩ := PowerlessRelativeClassSequenceWellOrderAmbient.exists_l hω hP
  obtain ⟨N, _, hNRead⟩ := PowerlessRelativeClassOmegaWellOrder.exists_l hω
  have hN := PowerlessRelativeClassOmegaAmbientOrder.of_comparison_l hω hNRead
  obtain ⟨I, K, hI, hK, _⟩ := PowerlessRelativeClassLexicographicAmbient.exists_l hN hT
  obtain ⟨J, U, hJ, hU, _⟩ := PowerlessRelativeClassLexicographicAmbient.exists_l hN hK
  let η : Env 𝒩 [] [.set, .set, .set, .set, .set] :=
    (((((Env.empty).pushFree R).pushFree I).pushFree S).pushFree A).pushFree ω
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] := query_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
    (.fvar .here) (.fvar (.there .here))
  obtain ⟨Q, hQ⟩ := PowerlessRelativeClassRelationalGraph.exists_l
    (φ := φ) (query_delta_l _ _ _ _ _ _ _) η J A
  have hRead (t x : type_l hℳ B) : value_l (ℳ := 𝒩) Q t x ↔
      SecondOrderQuotient.mem_l hℳ t.val J.val ∧ SecondOrderQuotient.mem_l hℳ x.val A.val ∧
        query_l (ℳ₀ := 𝒩) ω A S I R t x :=
    (hQ t x).trans (and_congr Iff.rfl (and_congr Iff.rfl (query_formula_l _ _ _ _ _ _ _ _)))
  obtain ⟨Y, F, hF, hOnto, _, hRange⟩ := PowerlessRelativeClassRowFamily.exists_l J A Q
  obtain ⟨G, hG, hInject, _⟩ := PowerlessRelativeClassWellOrderSection.exists_l hF
    (PowerlessRelativeClassAmbientWellOrder.restrict_l hU) hOnto
  obtain ⟨L, hL, _⟩ := PowerlessRelativeClassWellOrderPullbackAmbient.exists_l hG hInject hU
  have hSlice {t e p : type_l hℳ B}
      (he : SecondOrderQuotient.mem_l hℳ e.val ω.val) (hp : SecondOrderQuotient.mem_l hℳ p.val I.val)
      (ht : ordered_l (ℳ := 𝒩) e p t) (Z : type_l hℳ B) :
      PowerlessRelativeClassRowFamily.row_l (ℳ₀ := 𝒩) A Q t Z ↔
        PowerlessRelativeClassSatisfactionFamilyWellOrder.slice_l (ℳ₀ := 𝒩) ω A S e R p Z := by
    have htJ := (hJ t).mpr ⟨e, p, he, hp, ht⟩
    have hPoint (x : type_l hℳ B) :
        (SecondOrderQuotient.mem_l hℳ x.val A.val ∧ value_l (ℳ := 𝒩) Q t x) ↔
          (SecondOrderQuotient.mem_l hℳ x.val A.val ∧
            PowerlessRelativeClassSatisfactionRows.query_l (ℳ₀ := 𝒩) ω A S e R p x) := by
      apply and_congr_right
      intro hx
      exact (hRead t x).trans ⟨fun h => (read_l he hp ht).mp h.2.2,
        fun h => ⟨htJ, hx, (read_l he hp ht).mpr h⟩⟩
    exact ⟨fun h x => (h x).trans (hPoint x), fun h x => (h x).trans (hPoint x).symm⟩
  refine ⟨S, I, Y, L, hS, hI, ?_, hL⟩
  intro Z
  constructor
  · intro hZ
    obtain ⟨t, ht, hRow⟩ := (hRange Z).mp hZ
    obtain ⟨e, p, he, hp, hPair⟩ := (hJ t).mp ht
    exact ⟨e, p, he, hp, (hSlice he hp hPair Z).mp hRow⟩
  · rintro ⟨e, p, he, hp, hSliceZ⟩
    obtain ⟨t, ht⟩ := SecondOrderPairObjects.ordered_exists_l hℳ e.val p.val
    let t' : type_l hℳ B := ⟨t, PowerlessRelativeClassPair.ordered_l hℳ hBase e.property p.property ht⟩
    have ht' : ordered_l (ℳ := 𝒩) e p t' :=
      (PowerlessRelativeClassFunctionAbsolute.ordered_l e p t').mpr ht
    exact (hRange Z).mpr ⟨t', (hJ t').mpr ⟨e, p, he, hp, ht'⟩,
      (hSlice he hp ht' Z).mpr hSliceZ⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSatisfactionAllSlotsAmbient
