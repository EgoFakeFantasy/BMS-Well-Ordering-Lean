import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionAllSlotsAmbient
import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionQueryUnique
import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionIndexCanonical

/-! # 全槽 Sat 子集族的精确规范序构造

保留全部辅助规格，尤其全环境查询读值与规范比较图的精确成员。
由此可消费固定编码的 Sat 唯一性，而不把任意像集良序当成规范序。
仍需将该序限制到原 Def，并证明后继步骤的统一界和历史存在。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSatisfactionAllSlotsCanonical

open Logic FirstOrder ThirdOrderSemantics
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassSatisfactionAllSlots (query_m query_l query_delta_l query_formula_l read_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
    ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

local notation "𝒞" => structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l {ω A P : type_l hℳ B}
    (hω : omega_l (ℳ := 𝒞) ω) (hP : wellOrder_l (ℳ := 𝒱) A.val P.val) (R : type_l hℳ B) :
    ∃ S I J U Q Y L : type_l hℳ B, PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒞) ω A S ∧
      (∀ p : type_l hℳ B, SecondOrderQuotient.mem_l hℳ p.val I.val ↔ ∃ c f : type_l hℳ B,
        SecondOrderQuotient.mem_l hℳ c.val ω.val ∧ SecondOrderQuotient.mem_l hℳ f.val S.val ∧
          ordered_l (ℳ := 𝒞) c f p) ∧
      (∀ t : type_l hℳ B, SecondOrderQuotient.mem_l hℳ t.val J.val ↔ ∃ e p : type_l hℳ B,
        SecondOrderQuotient.mem_l hℳ e.val ω.val ∧ SecondOrderQuotient.mem_l hℳ p.val I.val ∧
          ordered_l (ℳ := 𝒞) e p t) ∧
      wellOrder_l (ℳ := 𝒱) J.val U.val ∧
      (∀ t x, value_l (ℳ := 𝒱) Q.val t x ↔ SecondOrderQuotient.mem_l hℳ t J.val ∧
        SecondOrderQuotient.mem_l hℳ x A.val ∧ query_l (ℳ₀ := 𝒱) ω.val A.val S.val I.val R.val t x) ∧
      PowerlessRelativeClassRowOrderCanonical.family_l (ℳ₀ := 𝒞) J A Q Y ∧
      PowerlessRelativeClassRowOrderCanonical.graph_l (ℳ₀ := 𝒱) J.val U.val A.val Q.val Y.val L.val ∧
      wellOrder_l (ℳ := 𝒱) Y.val L.val ∧
      PowerlessRelativeClassSatisfactionAllSlots.family_l (ℳ₀ := 𝒞) ω A S I R Y ∧
      PowerlessRelativeClassSatisfactionIndexCanonical.spec_l (ℳ₀ := 𝒞) ω A P S I J U := by
  obtain ⟨S, I, J, U, hIndex, hU⟩ := PowerlessRelativeClassSatisfactionIndexCanonical.exists_l hω hP
  have hS := hIndex.1
  have hI := hIndex.2.1
  have hJ := hIndex.2.2.1
  let η : Env 𝒞 [] [.set, .set, .set, .set, .set] :=
    (((((Env.empty).pushFree R).pushFree I).pushFree S).pushFree A).pushFree ω
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] := query_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
    (.fvar .here) (.fvar (.there .here))
  obtain ⟨Q, hQ⟩ := PowerlessRelativeClassRelationalGraph.exists_ambient_l
    (φ := φ) (query_delta_l _ _ _ _ _ _ _) η J A
  have hRawφ t x : φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree x).pushFree t) ↔
      query_l (ℳ₀ := 𝒱) ω.val A.val S.val I.val R.val t x := query_formula_l _ _ _ _ _ _ _ _
  have hRaw t x : value_l (ℳ := 𝒱) Q.val t x ↔ SecondOrderQuotient.mem_l hℳ t J.val ∧
      SecondOrderQuotient.mem_l hℳ x A.val ∧ query_l (ℳ₀ := 𝒱) ω.val A.val S.val I.val R.val t x :=
    (hQ t x).trans (and_congr Iff.rfl (and_congr Iff.rfl (hRawφ t x)))
  have hClassφ (t x : type_l hℳ B) : φ.satisfies ((η.pushFree x).pushFree t) ↔
      query_l (ℳ₀ := 𝒞) ω A S I R t x := query_formula_l _ _ _ _ _ _ _ _
  have hRead (t x : type_l hℳ B) : value_l (ℳ := 𝒞) Q t x ↔
      SecondOrderQuotient.mem_l hℳ t.val J.val ∧ SecondOrderQuotient.mem_l hℳ x.val A.val ∧
        query_l (ℳ₀ := 𝒞) ω A S I R t x :=
    (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) Q t x).trans
      ((hQ t.val x.val).trans (and_congr Iff.rfl (and_congr Iff.rfl
        ((PowerlessRelativeClassRelationAmbientMembers.formula_absolute_l
          (query_delta_l _ _ _ _ _ _ _) η t x).symm.trans (hClassφ t x)))))
  obtain ⟨Y, L, hFamily, hGraph, hOrder⟩ := PowerlessRelativeClassRowOrderCanonical.exists_l J A Q U hU
  have hSlice {t e p : type_l hℳ B}
      (he : SecondOrderQuotient.mem_l hℳ e.val ω.val) (hp : SecondOrderQuotient.mem_l hℳ p.val I.val)
      (ht : ordered_l (ℳ := 𝒞) e p t) (Z : type_l hℳ B) :
      PowerlessRelativeClassRowFamily.row_l (ℳ₀ := 𝒞) A Q t Z ↔
        PowerlessRelativeClassSatisfactionFamilyWellOrder.slice_l (ℳ₀ := 𝒞) ω A S e R p Z := by
    have htJ := (hJ t).mpr ⟨e, p, he, hp, ht⟩
    have hPoint (x : type_l hℳ B) :
        (SecondOrderQuotient.mem_l hℳ x.val A.val ∧ value_l (ℳ := 𝒞) Q t x) ↔
          (SecondOrderQuotient.mem_l hℳ x.val A.val ∧
            PowerlessRelativeClassSatisfactionRows.query_l (ℳ₀ := 𝒞) ω A S e R p x) := by
      apply and_congr_right
      intro hx
      exact (hRead t x).trans ⟨fun h => (read_l he hp ht).mp h.2.2,
        fun h => ⟨htJ, hx, (read_l he hp ht).mpr h⟩⟩
    exact ⟨fun h x => (h x).trans (hPoint x), fun h x => (h x).trans (hPoint x).symm⟩
  refine ⟨S, I, J, U, Q, Y, L, hS, hI, hJ, hU, hRaw, hFamily, hGraph, hOrder, ?_, hIndex⟩
  intro Z
  constructor
  · intro hZ
    obtain ⟨t, ht, hRow⟩ := (hFamily Z).mp hZ
    obtain ⟨e, p, he, hp, hPair⟩ := (hJ t).mp ht
    exact ⟨e, p, he, hp, (hSlice he hp hPair Z).mp hRow⟩
  · rintro ⟨e, p, he, hp, hSliceZ⟩
    obtain ⟨t, ht⟩ := SecondOrderPairObjects.ordered_exists_l hℳ e.val p.val
    let t' : type_l hℳ B := ⟨t, PowerlessRelativeClassPair.ordered_l hℳ hBase e.property p.property ht⟩
    have ht' : ordered_l (ℳ := 𝒞) e p t' :=
      (PowerlessRelativeClassFunctionAbsolute.ordered_l e p t').mpr ht
    exact (hFamily Z).mpr ⟨t', (hJ t').mpr ⟨e, p, he, hp, ht'⟩,
      (hSlice he hp ht' Z).mpr hSliceZ⟩

#print axioms exists_l

/-- 全环境查询值相同，则所有规范载体和最终比较图同时唯一。 -/
theorem unique_l {ω A P S I J U Q Y L S' I' J' U' Q' Y' L' : type_l hℳ B}
    (hIndex : PowerlessRelativeClassSatisfactionIndexCanonical.spec_l (ℳ₀ := 𝒞) ω A P S I J U)
    (hIndex' : PowerlessRelativeClassSatisfactionIndexCanonical.spec_l (ℳ₀ := 𝒞) ω A P S' I' J' U')
    (hQ : ∀ t x, value_l (ℳ := 𝒱) Q.val t x ↔ value_l (ℳ := 𝒱) Q'.val t x)
    (hFamily : PowerlessRelativeClassRowOrderCanonical.family_l (ℳ₀ := 𝒞) J A Q Y)
    (hFamily' : PowerlessRelativeClassRowOrderCanonical.family_l (ℳ₀ := 𝒞) J' A Q' Y')
    (hGraph : PowerlessRelativeClassRowOrderCanonical.graph_l (ℳ₀ := 𝒱) J.val U.val A.val Q.val Y.val L.val)
    (hGraph' : PowerlessRelativeClassRowOrderCanonical.graph_l (ℳ₀ := 𝒱) J'.val U'.val A.val Q'.val Y'.val L'.val) :
    S = S' ∧ I = I' ∧ J = J' ∧ U = U' ∧ Y = Y' ∧ L = L' := by
  obtain ⟨hS, hI, hJ, hU⟩ := PowerlessRelativeClassSatisfactionIndexCanonical.unique_l hIndex hIndex'
  subst S'
  subst I'
  subst J'
  subst U'
  have hClassQ (t x : type_l hℳ B) : value_l (ℳ := 𝒞) Q t x ↔ value_l (ℳ := 𝒞) Q' t x :=
    (PowerlessRelativeClassFunctionAbsolute.value_l Q t x).trans
      ((hQ t.val x.val).trans (PowerlessRelativeClassFunctionAbsolute.value_l Q' t x).symm)
  have hY : Y' = Y := by
    apply (PowerlessRelativeClassStructure.ext_l hℳ B hBase).eq_of_same_members
    intro y
    constructor
    · intro hy
      obtain ⟨i, hi, hRow⟩ := (hFamily' y).mp hy
      exact (hFamily y).mpr ⟨i, hi,
        (PowerlessRelativeClassRowOrderCanonical.row_congr_l (ℳ₀ := 𝒞) (A := A) hClassQ i y).mpr hRow⟩
    · intro hy
      obtain ⟨i, hi, hRow⟩ := (hFamily y).mp hy
      exact (hFamily' y).mpr ⟨i, hi,
        (PowerlessRelativeClassRowOrderCanonical.row_congr_l (ℳ₀ := 𝒞) (A := A) hClassQ i y).mp hRow⟩
  subst Y'
  exact ⟨rfl, rfl, rfl, rfl, rfl, Subtype.ext (PowerlessRelativeClassSatisfactionQueryUnique.orders_l hQ hGraph hGraph')⟩

#print axioms unique_l

/-- 固定一个合法编码包后，两张完整 Sat 产生同一行族及同一规范序。 -/
theorem for_sat_l (K : PowerlessBMSQuotientCoding.source_coding_l hℳ)
    {ω A P e t₁ t₂ t₃ Pair Valid R R' S I J U Q Y L S' I' J' U' Q' Y' L' : type_l hℳ B}
    (hω : ω.val = K.omega)
    (he : e.val = PowerlessFormulaValidityReading.code_l K (SecondOrderModel.zero_l ℳ))
    (hTags : PowerlessEvaluationTags.tags_l (ℳ := 𝒞) e t₁ t₂ t₃)
    (hPairMap : map_l (ℳ := 𝒱) Pair.val K.omega K.omega)
    (hPair : PowerlessBMSQuotientPairingBounds.spec_l K Pair.val)
    {V : SecondOrderModel.set_l ℳ} (hV : SecondOrderTriangularFormulaSyntax.spec_l V)
    (hValid : ∀ c N, value_l (ℳ := 𝒱) Valid.val c N ↔ PowerlessRelationalCodeValidity.valid_l K V c N)
    (hR : PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒞) ω A e t₁ t₂ t₃ Pair Valid R)
    (hR' : PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒞) ω A e t₁ t₂ t₃ Pair Valid R')
    (hIndex : PowerlessRelativeClassSatisfactionIndexCanonical.spec_l (ℳ₀ := 𝒞) ω A P S I J U)
    (hIndex' : PowerlessRelativeClassSatisfactionIndexCanonical.spec_l (ℳ₀ := 𝒞) ω A P S' I' J' U')
    (hRead : ∀ t x, value_l (ℳ := 𝒱) Q.val t x ↔ SecondOrderQuotient.mem_l hℳ t J.val ∧
      SecondOrderQuotient.mem_l hℳ x A.val ∧ query_l (ℳ₀ := 𝒱) ω.val A.val S.val I.val R.val t x)
    (hRead' : ∀ t x, value_l (ℳ := 𝒱) Q'.val t x ↔ SecondOrderQuotient.mem_l hℳ t J'.val ∧
      SecondOrderQuotient.mem_l hℳ x A.val ∧ query_l (ℳ₀ := 𝒱) ω.val A.val S'.val I'.val R'.val t x)
    (hFamily : PowerlessRelativeClassRowOrderCanonical.family_l (ℳ₀ := 𝒞) J A Q Y)
    (hFamily' : PowerlessRelativeClassRowOrderCanonical.family_l (ℳ₀ := 𝒞) J' A Q' Y')
    (hGraph : PowerlessRelativeClassRowOrderCanonical.graph_l (ℳ₀ := 𝒱) J.val U.val A.val Q.val Y.val L.val)
    (hGraph' : PowerlessRelativeClassRowOrderCanonical.graph_l (ℳ₀ := 𝒱) J'.val U'.val A.val Q'.val Y'.val L'.val) :
    Y = Y' ∧ L = L' := by
  obtain ⟨hS, hI, hJ, hU⟩ := PowerlessRelativeClassSatisfactionIndexCanonical.unique_l hIndex hIndex'
  subst S'
  subst I'
  subst J'
  subst U'
  have hQ := PowerlessRelativeClassSatisfactionQueryUnique.queries_l
    K hω he hTags hPairMap hPair hV hValid hR hR' hRead hRead'
  exact (unique_l hIndex hIndex' hQ hFamily hFamily' hGraph hGraph').2.2.2.2

#print axioms for_sat_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSatisfactionAllSlotsCanonical
