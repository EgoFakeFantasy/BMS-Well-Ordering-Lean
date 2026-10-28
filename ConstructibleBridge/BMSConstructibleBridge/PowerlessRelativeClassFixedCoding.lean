import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionSpecification
import BMSConstructibleBridge.PowerlessRelativeClassTriangular

/-! # 改换辅助基底时保持原来的编码包

已给定的三角图由同一 K 的逐数规格及全坐标函数守卫唯一确定。
在新相对类中构造比较图，再以外延相等恢复原图；没有替换全局编码。
完整 Sat 逐域在 Prop 内构造，不要求整类满足 PowerlessTheory。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFixedCoding

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
    ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

local notation "𝒞" => structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 同编码规格使给定原图具有新辅助类中的完整三角递推。 -/
theorem triangular_l (K : source_coding_l hℳ) {ω e T : type_l hℳ B}
    (hω : ω.val = K.omega) (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hMap : map_l (ℳ := 𝒱) T.val K.omega K.omega)
    (hSpec : PowerlessBMSQuotientPairingBounds.spec_l K T.val) :
    PowerlessTriangular.triangular_l (ℳ := 𝒞) ω e T := by
  have hΩ : omega_l (ℳ := 𝒞) ω :=
    (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mpr (hω.symm ▸ K.omega_spec)
  obtain ⟨S, hS, _⟩ := PowerlessRelativeClassFiniteSequencesDerives.exists_ambient_l
    (hBase := hBase) (X := ω) hΩ
  rw [hω] at hS
  obtain ⟨U, hU, hSpecU⟩ := PowerlessRelativeClassTriangular.exists_spec_l K ω e S hω he hS
  have hMapU : map_l (ℳ := 𝒱) U.val K.omega K.omega := by
    simpa only [ThirdOrderSemantics.map_l, ThirdOrderSemantics.member_l, ThirdOrderSemantics.value_l,
      ThirdOrderSemantics.ordered_l, ThirdOrderSemantics.pair_l, SecondOrderQuotient.structure_l,
      SecondOrderFunctionObjects.map_l, SecondOrderFunctionObjects.value_l,
      SecondOrderPairObjects.ordered_l, SecondOrderPairObjects.pair_l, hω]
      using (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) U ω ω).mp hU.1
  have hRead (x y : SecondOrderQuotient.type_l hℳ)
      (hx : SecondOrderQuotient.mem_l hℳ x K.omega)
      (hy : SecondOrderQuotient.mem_l hℳ y K.omega) :
      value_l (ℳ := 𝒱) U.val x y ↔ value_l (ℳ := 𝒱) T.val x y := by
    obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨x, hx⟩
    obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨y, hy⟩
    have hi' : (numberCode_l K i).val = x := congrArg Subtype.val hi
    have hj' : (numberCode_l K j).val = y := congrArg Subtype.val hj
    simpa only [hi', hj'] using (hSpecU i j).trans (hSpec i j).symm
  have hEq : U = T := Subtype.ext (PowerlessBMSQuotientRecursion.map_ext_l hMapU hMap (by
    intro x y
    constructor
    · intro hxy
      have hMem := PowerlessBMSQuotientRecursion.value_mem_l hMapU hxy
      exact (hRead x y hMem.1 hMem.2).mp hxy
    · intro hxy
      have hMem := PowerlessBMSQuotientRecursion.value_mem_l hMap hxy
      exact (hRead x y hMem.1 hMem.2).mpr hxy))
  exact hEq ▸ hU

/-- 类中的同一编码包给每个域完整 Sat，不另选合法性图或配数图。 -/
theorem satisfaction_l (K : source_coding_l hℳ) {ω A e t₁ t₂ t₃ T Valid : type_l hℳ B}
    (hω : ω.val = K.omega) (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hTags : PowerlessEvaluationTags.tags_l (ℳ := 𝒱) e.val t₁.val t₂.val t₃.val)
    (hMap : map_l (ℳ := 𝒱) T.val K.omega K.omega)
    (hSpec : PowerlessBMSQuotientPairingBounds.spec_l K T.val)
    {V : SecondOrderModel.set_l ℳ} (hV : SecondOrderTriangularFormulaSyntax.spec_l V)
    (hValid : ∀ c N, value_l (ℳ := 𝒱) Valid.val c N ↔ PowerlessRelationalCodeValidity.valid_l K V c N) :
    ∃ R : type_l hℳ B,
      PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒞) ω A e t₁ t₂ t₃ T Valid R := by
  have hΩ : omega_l (ℳ := 𝒞) ω :=
    (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mpr (hω.symm ▸ K.omega_spec)
  have hTagsClass : PowerlessEvaluationTags.tags_l (ℳ := 𝒞) e t₁ t₂ t₃ :=
    ⟨(PowerlessRelativeClassOmegaAbsolute.empty_l (hBase := hBase) e).mpr hTags.1,
      (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) e t₁).mpr hTags.2.1,
      (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) t₁ t₂).mpr hTags.2.2.1,
      (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) t₂ t₃).mpr hTags.2.2.2⟩
  obtain ⟨S, G, hSystem⟩ := PowerlessRelativeClassEvaluationSystem.exists_for_coding_l K hΩ hω he
    hTagsClass (triangular_l K hω he hMap hSpec) hMap hSpec A
  obtain ⟨R, hR⟩ := PowerlessSatisfactionGraph.exists_l (hBase := hBase) ω A S Valid G
  exact ⟨R, PowerlessRelativeClassSatisfactionSpecification.instance_l hR K hω
    (PowerlessRelativeClassSequenceAbsolute.spec_l hΩ hSystem.2.2.2.1)
    hValid hSystem he hMap hSpec hV⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFixedCoding
