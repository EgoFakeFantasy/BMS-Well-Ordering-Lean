import BMSConstructibleBridge.PowerlessLegacyLegalIndexBounded
import BMSConstructibleBridge.PowerlessRelativeClassDeltaSeparation

/-! # 原 Def 全部合法索引的实际 Class 集合

在给定 Class 数值幂图、旧合法图和完整数字序列母集中，用纯 Δ₀ 分离
取得精确的原合法索引子集。原商中任意非数字坐标没有额外成员；全部
内部数码均被覆盖。这是原 Def 统一行族的指标，不是整个 Def 对象。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassLegacyLegalIndices

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessFormulaValidityReading (code_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

include hBase

theorem exists_l (K : source_coding_l hℳ) {ω N P G : type_l hℳ B}
    (hω : ω.val = K.omega)
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega K.omega N.val) {E V : SecondOrderModel.set_l ℳ}
    (hP : ∀ n m, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) P.val
      (code_l K n) (code_l K m) ↔ SecondOrderPairing.relation_l E n m)
    (hG : ∀ n m, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G.val
      (code_l K n) (code_l K m) ↔ SecondOrderPairing.relation_l V n m) :
    ∃ I : type_l hℳ B, ∀ x : SecondOrderQuotient.type_l hℳ,
      mem_l hℳ x I.val ↔ ∃ i, x = code_l K i ∧ SecondOrderLegalFormulaIndex.spec_l V E i := by
  let e : type_l hℳ B := ⟨code_l K (SecondOrderModel.zero_l ℳ),
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property
      (by rw [hω]; exact (numberCode_l K (SecondOrderModel.zero_l ℳ)).property)⟩
  let η : Env (structure_l hℳ B hBase) [] [.set, .set, .set, .set, .set] :=
    (((((Env.empty).pushFree G).pushFree P).pushFree N).pushFree e).pushFree ω
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set] :=
    PowerlessLegacyLegalIndexBounded.formula_m (.fvar (.there .here))
      (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here)))))) (.fvar .here)
  have hφ : Formula.IsDelta0 membershipLevyBound φ :=
    PowerlessLegacyLegalIndexBounded.delta_l _ _ _ _ _ _
  have hRead (x : type_l hℳ B) : φ.satisfies (η.pushFree x) ↔
      PowerlessLegacyLegalIndexBounded.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
        K.omega (code_l K (SecondOrderModel.zero_l ℳ)) N.val P.val G.val x.val := by
    have h := (PowerlessRelativeClassBounded.formula_l hφ (η.pushFree x)).trans
      (PowerlessLegacyLegalIndexBounded.formula_l
        (PowerlessRelativeClassRelativization.env_l (η.pushFree x)) _ _ _ _ _ _)
    change φ.satisfies (η.pushFree x) ↔ PowerlessLegacyLegalIndexBounded.holds_l
      (𝒩 := SecondOrderQuotient.structure_l hℳ) ω.val
        (code_l K (SecondOrderModel.zero_l ℳ)) N.val P.val G.val x.val at h
    simpa only [hω] using h
  obtain ⟨I, hI⟩ := PowerlessRelativeClassDeltaSeparation.exists_l hφ η ω
  refine ⟨I, fun x => ⟨?_, ?_⟩⟩
  · intro hx
    let x' : type_l hℳ B := ⟨x,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase I.property hx⟩
    obtain ⟨hxω, hLegal⟩ := (hI x').mp hx
    have hxω' : mem_l hℳ x K.omega := by simpa only [hω] using hxω
    obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨x, hxω'⟩
    have hX : x = code_l K i := (congrArg Subtype.val hi).symm
    have hCheck := (hRead x').mp hLegal
    change PowerlessLegacyLegalIndexBounded.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega
      (code_l K (SecondOrderModel.zero_l ℳ)) N.val P.val G.val x at hCheck
    rw [hX] at hCheck
    exact ⟨i, hX, (PowerlessLegacyLegalIndexBounded.reading_l K hN hP hG i).mp hCheck⟩
  · rintro ⟨i, rfl, hLegal⟩
    let x' : type_l hℳ B := ⟨code_l K i,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property
        (by rw [hω]; exact (numberCode_l K i).property)⟩
    exact (hI x').mpr ⟨by rw [hω]; exact (numberCode_l K i).property,
      (hRead x').mpr ((PowerlessLegacyLegalIndexBounded.reading_l K hN hP hG i).mpr hLegal)⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassLegacyLegalIndices
