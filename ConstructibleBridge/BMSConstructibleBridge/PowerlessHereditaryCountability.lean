import BMSConstructibleBridge.PowerlessHereditaryFunctionAbsolute
import BMSConstructibleBridge.PowerlessHereditaryProduct
import BMSConstructibleBridge.PowerlessHereditaryOrdinalCountability
import BMSConstructibleBridge.PowerlessHereditaryOmegaAbsolute
import BMSConstructibleBridge.PowerlessHereditaryRelativization
import BMSConstructibleBridge.SecondOrderCountabilityAxiom

/-! # 实际遗传子模型中的集合单射可数性

純隶属 ℒ，原 Z₂ 背景及原 Derives 核。每个遗传对象已有 Class
最小编号单射；干净图以同一遗传对象与内部 ω 的积为母界，因而该
原单射图也遗传。不是把环境可数性或 Class 单射冒充遗传域中的函数。
原可数性公理的整句回传已完成；Collection 和最终 BMS 良序仍另待证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryCountability

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessHereditaryStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩₁" => structure_l hℳ B hBase

/-- 同一 Class 单射的整张图进入遗传域，不换编号。 -/
theorem exists_l (K : source_coding_l hℳ) (O A : type_l hℳ B)
    (hω : SecondOrderOmega.omega_l hℳ O.val) :
    ∃ F : type_l hℳ B, map_l (ℳ := 𝒩₁) F A O ∧ injective_l (ℳ := 𝒩₁) F := by
  obtain ⟨f, hf, hMap, hInjective⟩ :=
    PowerlessHereditaryOrdinalCountability.countable_of_hereditary_l
      (hBase := hBase) K hω A.property
  have hfHC := PowerlessHereditaryProduct.relation_l (hBase := hBase) A.property O.property hf hMap.1
  let F : type_l hℳ B := ⟨f, hfHC⟩
  refine ⟨F, (PowerlessHereditaryFunctionAbsolute.map_l (hBase := hBase) F A O).mpr hMap, ?_⟩
  intro x z y hxy hzy
  exact Subtype.ext (hInjective x.val z.val y.val
    ((PowerlessHereditaryFunctionAbsolute.value_l (hBase := hBase) F x y).mp hxy)
    ((PowerlessHereditaryFunctionAbsolute.value_l (hBase := hBase) F z y).mp hzy))

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    SecondOrderCountabilityAxiom.formula_m.TrueIn (structure_l hℳ B hBase) := by
  simp only [SecondOrderCountabilityAxiom.formula_m, Formula.TrueIn, Formula.satisfies,
    omega_formula_l, map_formula_l, injective_formula_l]
  change ∀ A : type_l hℳ B, ∃ O F : type_l hℳ B,
    omega_l (ℳ := structure_l hℳ B hBase) O ∧
      map_l (ℳ := structure_l hℳ B hBase) F A O ∧
        injective_l (ℳ := structure_l hℳ B hBase) F
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  let O : type_l hℳ B := ⟨K.omega, PowerlessHereditaryOmega.member_l hℳ hBase K.omega_spec⟩
  intro A
  obtain ⟨F, hF, hInjective⟩ := exists_l (hBase := hBase) K O A K.omega_spec
  exact ⟨O, F, (PowerlessHereditaryOmegaAbsolute.omega_l (hBase := hBase) O).mpr K.omega_spec,
    hF, hInjective⟩

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m
      (PowerlessHereditaryRelativization.guarded_m SecondOrderCountabilityAxiom.formula_m)) :=
  PowerlessHereditaryRelativization.derives_m _ (fun _ h𝒩 B hBase => models_l h𝒩 B hBase)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryCountability
