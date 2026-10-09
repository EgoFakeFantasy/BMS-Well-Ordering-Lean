import BMSConstructibleBridge.PowerlessFiniteProgramOutputSyntax

/-! # 同一内部历史及指定存储坐标的输出读数

纯隶属 ℒ，背景原 Z₂。精确认同原 run/output 矩阵：历史图和陪域
的 Class 资格由原正文取得，末状态及图坐标从实际取值取得。
无候选时的 B 分支比较全部 raw 输出，不把缺省值当作真实运行。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassProgramOutputReading

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ z, mem_l hℳ z B → ∀ t, mem_l hℳ t z → mem_l hℳ t B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => structure_l hℳ B hBase
local notation "M" => type_l hℳ B

theorem run_l {Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (ψ : Formula ℒ [] (.set :: .set :: Θ))
    (η : Env 𝒩₀ [] Δ) (ξ : Env 𝒱 [] Θ)
    (hRelation : ∀ x y : M, ψ.satisfies ((ξ.pushFree x.val).pushFree y.val) ↔
      φ.satisfies ((η.pushFree x).pushFree y)) (ω e a n k y : M) :
    PowerlessFiniteProgramOutputSyntax.run_l φ η ω e a n k y ↔
      PowerlessRelativeFiniteProgramOutput.run_l ψ ξ B ω.val e.val a.val n.val k.val y.val := by
  constructor
  · rintro ⟨S, D, F, s, E, g, hTrace, hs, hv, hy⟩
    exact ⟨S.val, D.val, F.val, s.val, E.val, g.val, D.property, F.property,
      (PowerlessRelativeClassDefinableTraceReading.trace_l φ ψ η ξ hRelation e a n S D F).mp hTrace,
      (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) F n s).mp hs,
      (PowerlessRelativeClassProgramStepReading.valid_l (hBase := hBase) ω n E g s).mp hv,
      (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) g k y).mp hy⟩
  · rintro ⟨S, D, F, s, E, g, hDC, hFC, hTrace, hs, hv, hy⟩
    let S₀ : M := ⟨S, PowerlessRelativeClassFunctionAppend.adjoin_class_l
      hBase n.property n.property hTrace.1⟩
    let D₀ : M := ⟨D, hDC⟩
    let F₀ : M := ⟨F, hFC⟩
    let s₀ : M := ⟨s, (PowerlessRelativeClassValueCoordinates.value_l hBase F₀ hs).2⟩
    let E₀ : M := ⟨E, hv.2.2.2.1⟩
    let g₀ : M := ⟨g, hv.2.2.2.2.1⟩
    exact ⟨S₀, D₀, F₀, s₀, E₀, g₀,
      (PowerlessRelativeClassDefinableTraceReading.trace_l φ ψ η ξ hRelation e a n S₀ D₀ F₀).mpr hTrace,
      (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) F₀ n s₀).mpr hs,
      (PowerlessRelativeClassProgramStepReading.valid_l (hBase := hBase) ω n E₀ g₀ s₀).mpr hv,
      (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) g₀ k y).mpr hy⟩

theorem output_l {Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (ψ : Formula ℒ [] (.set :: .set :: Θ))
    (η : Env 𝒩₀ [] Δ) (ξ : Env 𝒱 [] Θ)
    (hRelation : ∀ x y : M, ψ.satisfies ((ξ.pushFree x.val).pushFree y.val) ↔
      φ.satisfies ((η.pushFree x).pushFree y)) (ω e a n k y : M) :
    PowerlessFiniteProgramOutputSyntax.output_l φ η
      ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ ω e a n k y ↔
      PowerlessRelativeFiniteProgramOutput.output_l ψ ξ B ω.val e.val a.val n.val k.val y.val := by
  have hSome : (∃ z, PowerlessRelativeFiniteProgramOutput.run_l ψ ξ B
      ω.val e.val a.val n.val k.val z) ↔
      ∃ z : M, PowerlessFiniteProgramOutputSyntax.run_l φ η ω e a n k z := by
    constructor
    · rintro ⟨z, hz⟩
      let z₀ : M := ⟨z, PowerlessRelativeFiniteProgramOutput.run_class_l (hℳ := hℳ) ψ ξ hBase hz⟩
      exact ⟨z₀, (run_l φ ψ η ξ hRelation ω e a n k z₀).mpr hz⟩
    · rintro ⟨z, hz⟩
      exact ⟨z.val, (run_l φ ψ η ξ hRelation ω e a n k z).mp hz⟩
  have hEqual : y = ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ ↔ y.val = B :=
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hDisj := or_congr (run_l φ ψ η ξ hRelation ω e a n k y)
    (and_congr (not_congr hSome.symm) hEqual)
  exact ⟨fun h => ⟨y.property, hDisj.mp h⟩, fun h => hDisj.mpr h.2⟩

#print axioms run_l
#print axioms output_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassProgramOutputReading
