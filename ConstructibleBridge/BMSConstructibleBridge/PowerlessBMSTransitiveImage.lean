import BMSConstructibleBridge.PowerlessBMSClassCollapse
import BMSConstructibleBridge.SecondOrderGraftSemantics

/-!
# 自然数索引的传递类像是内部集合

给定实际纯公式定义的总单值类映射，若输出类对隶属封闭，则其精确值域
由一张实际内部良基数图的全部根组装得到。没有假定 Collection 或类选择。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSTransitiveImage

open Logic FirstOrder PowerlessBMSQuotientCoding

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private abbrev quotient_l := SecondOrderQuotient.structure_l hℳ

theorem exists_l (C : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env quotient_l [] Δ)
    (hTotal : ∀ n, ∃ y, φ.satisfies ((η.pushFree (numberCode_l C n).val).pushFree y))
    (hUnique : ∀ n y z,
      φ.satisfies ((η.pushFree (numberCode_l C n).val).pushFree y) →
      φ.satisfies ((η.pushFree (numberCode_l C n).val).pushFree z) → y = z)
    (hTrans : ∀ n y, φ.satisfies ((η.pushFree (numberCode_l C n).val).pushFree y) →
      ∀ z, SecondOrderQuotient.mem_l hℳ z y →
        ∃ m, φ.satisfies ((η.pushFree (numberCode_l C m).val).pushFree z)) :
    ∃ b : SecondOrderQuotient.type_l hℳ, ∀ y, SecondOrderQuotient.mem_l hℳ y b ↔
      ∃ n, φ.satisfies ((η.pushFree (numberCode_l C n).val).pushFree y) := by
  obtain ⟨R, hR, hWf⟩ := PowerlessBMSClassRelation.exists_l C φ η hTotal hUnique
  have hAgree := PowerlessBMSClassCollapse.agrees_l C φ η R hWf hUnique hR hTrans
  let ψ : Formula SecondOrderSyntax.signature_m [] [.num] :=
    .equal (.fvar .here) (.fvar .here)
  obtain ⟨P, hP⟩ := SecondOrderModel.comprehension_l hℳ ψ rfl Env.empty
  have hAll n : SecondOrderModel.mem_l n P := (hP n).mpr rfl
  obtain ⟨B, hB⟩ := SecondOrderGraftSemantics.exists_l hℳ R P (fun n _ => hWf n)
  refine ⟨SecondOrderQuotient.mk_l hℳ B, fun y => ?_⟩
  obtain ⟨Y, rfl⟩ := SecondOrderQuotient.surj_l hℳ y
  change SecondOrderGraph.mem_l Y B ↔ _
  rw [hB]
  constructor
  · rintro ⟨n, _, hYn⟩
    obtain ⟨y, hy⟩ := hTotal n
    have hY : SecondOrderQuotient.mk_l hℳ Y =
        SecondOrderQuotient.mk_l hℳ ⟨R, n, hWf n⟩ :=
      (SecondOrderQuotient.eq_iff_l hℳ Y _).mpr hYn
    rw [hAgree n y hy] at hY
    exact ⟨n, hY.symm ▸ hy⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, hAll n, (SecondOrderQuotient.eq_iff_l hℳ Y _).mp (hAgree n _ hn).symm⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSTransitiveImage
