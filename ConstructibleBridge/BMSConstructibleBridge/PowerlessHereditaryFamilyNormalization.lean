import BMSConstructibleBridge.PowerlessRootedFamilyNormalizationReading
import BMSConstructibleBridge.PowerlessHereditaryNumericRelation

/-! # 同一统一零根族的实际类内实数代表

纯隶属 ℒ，原 Z₂ 背景。以原族 U 为参数，纯有界图在 Class 内
分离，再编码成类内实数 V。全部内部数的读数等于旧规范化规格，
因此任意已有旧规范化 J 都由同一 V 读取，而非另换未认同的码。
V 是 ω 的 Class 子集，故实际遗传；此结论仍不推出解码集合遗传。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryFamilyNormalization

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩₀" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "M" => PowerlessRelativeClassStructure.type_l hℳ B

include hBase in
theorem coded_l (K : source_coding_l hℳ) (U : M)
    (hU : ∀ c, mem_l hℳ c U.val → mem_l hℳ c K.omega) {H : SecondOrderModel.set_l ℳ}
    (hTrace : setRel_l K ⟨U.val, hU⟩ H) :
    ∃ V : M, PowerlessHereditaryClass.member_l hℳ B V.val ∧
      ∃ hV : ∀ c, mem_l hℳ c V.val → mem_l hℳ c K.omega,
        ∃ J : SecondOrderModel.set_l ℳ, setRel_l K ⟨V.val, hV⟩ J ∧
          SecondOrderRootedRealFamilyNormalization.spec_l H J := by
  let O : M := ⟨K.omega, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)⟩
  let e : M := ⟨(numberCode_l K (SecondOrderModel.zero_l ℳ)).val,
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase O.property
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).property⟩
  let o : M := ⟨(numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).val,
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase O.property
      (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).property⟩
  obtain ⟨S, hS, _⟩ := PowerlessRelativeClassFiniteSequencesDerives.exists_ambient_l (hBase := hBase)
    (X := O) ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) O).mpr K.omega_spec)
  let η : Env 𝒩₀ [] [.set, .set, .set, .set, .set] :=
    Env.empty |>.pushFree U |>.pushFree S |>.pushFree o |>.pushFree e |>.pushFree O
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] :=
    PowerlessRootedFamilyNormalizationSyntax.body_m
      (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar .here) (.fvar (.there .here))
  obtain ⟨V, hVHC, hV, J, hVTrace, hRead⟩ := PowerlessHereditaryNumericRelation.coded_l K
    (φ := φ) (PowerlessRootedFamilyNormalizationSyntax.body_delta_m _ _ _ _ _ _ _) η
  have hSpec : SecondOrderRootedRealFamilyNormalization.spec_l H J := by
    intro i z
    have hφ := PowerlessRootedFamilyNormalizationSyntax.body_formula_l
      (((PowerlessRelativeClassRelativization.env_l η).pushFree (numberCode_l K z).val).pushFree
        (numberCode_l K i).val)
      (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar .here) (.fvar (.there .here))
    change φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree
      (numberCode_l K z).val).pushFree (numberCode_l K i).val) ↔
      PowerlessRootedFamilyNormalizationSyntax.body_l (𝒩 := 𝒱) K.omega e.val o.val S.val U.val
        (numberCode_l K i).val (numberCode_l K z).val at hφ
    exact (hRead i z).trans (hφ.trans
      (PowerlessRootedFamilyNormalizationReading.body_l K hS hU hTrace i z))
  exact ⟨V, hVHC, hV, J, hVTrace, hSpec⟩

include hBase in
/-- 保留调用端同一原规范化 J；关系外延性不是额外的配数满射假设。 -/
theorem same_l (K : source_coding_l hℳ) (U : M)
    (hU : ∀ c, mem_l hℳ c U.val → mem_l hℳ c K.omega) {H J : SecondOrderModel.set_l ℳ}
    (hTrace : setRel_l K ⟨U.val, hU⟩ H)
    (hJ : SecondOrderRootedRealFamilyNormalization.spec_l H J) :
    ∃ V : M, PowerlessHereditaryClass.member_l hℳ B V.val ∧
      ∃ hV : ∀ c, mem_l hℳ c V.val → mem_l hℳ c K.omega, setRel_l K ⟨V.val, hV⟩ J := by
  obtain ⟨V, hVHC, hV, J₀, hVTrace, hSpec⟩ := coded_l (hBase := hBase) K U hU hTrace
  have hEq : J₀ = J := SecondOrderRelations.ext_l hℳ J₀ J
    (fun i z => (hSpec i z).trans (hJ i z).symm)
  exact ⟨V, hVHC, hV, hEq ▸ hVTrace⟩

#print axioms coded_l
#print axioms same_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryFamilyNormalization
