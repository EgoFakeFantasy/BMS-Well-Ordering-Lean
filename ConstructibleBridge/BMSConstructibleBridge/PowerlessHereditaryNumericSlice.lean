import BMSConstructibleBridge.PowerlessHereditaryNumericRelation

/-! # 任意类内有界数谓词的遗传实数切片

实际 ω 上的 Class 分离给出整张数迹，输出的 ω 子集因而遗传。
自由参数只要求属于 Class；这里没有把任意类外实数放入环境。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryNumericSlice

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
    {φ : Formula ℒ [] (.set :: Δ)} (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (η : Env 𝒩₀ [] Δ) :
    ∃ V : M, PowerlessHereditaryClass.member_l hℳ B V.val ∧
      ∃ hV : ∀ c, mem_l hℳ c V.val → mem_l hℳ c K.omega,
        ∃ R : SecondOrderModel.set_l ℳ, setRel_l K ⟨V.val, hV⟩ R ∧
          ∀ n, SecondOrderModel.mem_l n R ↔
            φ.satisfies ((PowerlessRelativeClassRelativization.env_l η).pushFree (numberCode_l K n).val) := by
  let O : M := ⟨K.omega, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)⟩
  obtain ⟨V, hV⟩ := PowerlessRelativeClassDeltaSeparation.exists_l hφ η O
  have hSub : ∀ c, mem_l hℳ c V.val → mem_l hℳ c K.omega := by
    intro c hc
    let c₀ : M := ⟨c, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase V.property hc⟩
    exact ((hV c₀).mp hc).1
  obtain ⟨R, hTrace⟩ := PowerlessBMSQuotientReals.trace_exists_l K ⟨V.val, hSub⟩
  refine ⟨V, PowerlessHereditarySubset.member_l hℳ hBase
    (PowerlessHereditaryOmega.member_l hℳ hBase K.omega_spec) V.property hSub,
    hSub, R, hTrace, fun n => ?_⟩
  let n₀ : M := ⟨(numberCode_l K n).val,
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase O.property (numberCode_l K n).property⟩
  have hEnv : PowerlessRelativeClassRelativization.env_l (η.pushFree (sort := SetTheory.SetSort.set) n₀) =
      (PowerlessRelativeClassRelativization.env_l η).pushFree
        (sort := SetTheory.SetSort.set) n₀.val := by
    apply Env.ext
    · intro s v; nomatch v
    · intro s v; cases s; cases v <;> rfl
  have hAbs := PowerlessRelativeClassBounded.formula_l hφ (η.pushFree n₀)
  rw [hEnv] at hAbs
  refine (hTrace n).symm.trans ⟨fun h => hAbs.mp ((hV n₀).mp h).2, fun h => ?_⟩
  exact (hV n₀).mpr ⟨(numberCode_l K n).property, hAbs.mpr h⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryNumericSlice
