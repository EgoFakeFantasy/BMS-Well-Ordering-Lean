import BMSConstructibleBridge.PowerlessRelativeClassNumericGraph
import BMSConstructibleBridge.PowerlessRelativeClassRelationalGraph
import BMSConstructibleBridge.PowerlessHereditarySubset
import BMSConstructibleBridge.PowerlessHereditaryOmega

/-! # 任意实际类内有界数关系的遗传实数编码

参数和正文保持同一，允许关系多值、部分定义或空。先取得整张
Class 关系图，再作数编码；输出是真正 Class 内的 ω 子集，故遗传。
不把逐点数值资格替代整图存在性，不从 Type 选择函数拼接族。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryNumericRelation

open Logic FirstOrder StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩₀" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "M" => PowerlessRelativeClassStructure.type_l hℳ B

theorem coded_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    {φ : Formula ℒ [] (.set :: .set :: Δ)} (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (η : Env 𝒩₀ [] Δ) :
    ∃ V : M, PowerlessHereditaryClass.member_l hℳ B V.val ∧
      ∃ hV : ∀ c, mem_l hℳ c V.val → mem_l hℳ c K.omega,
        ∃ R : SecondOrderModel.set_l ℳ, setRel_l K ⟨V.val, hV⟩ R ∧
          ∀ n m, SecondOrderPairing.relation_l R n m ↔
            φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree
              (numberCode_l K m).val).pushFree (numberCode_l K n).val) := by
  let O : M := ⟨K.omega, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)⟩
  obtain ⟨Q, hQ⟩ := PowerlessRelativeClassRelationalGraph.exists_ambient_l hφ η O O
  obtain ⟨V, hV, R, hTrace, hRead⟩ :=
    PowerlessRelativeClassNumericGraph.coded_l (hBase := hBase) K Q
  refine ⟨V, PowerlessHereditarySubset.member_l hℳ hBase
    (PowerlessHereditaryOmega.member_l hℳ hBase K.omega_spec) V.property hV,
    hV, R, hTrace, fun n m => ?_⟩
  refine (hRead n m).trans ⟨fun h => ((hQ _ _).mp h).2.2, fun h => ?_⟩
  exact (hQ _ _).mpr ⟨(numberCode_l K n).property, (numberCode_l K m).property, h⟩

#print axioms coded_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryNumericRelation
