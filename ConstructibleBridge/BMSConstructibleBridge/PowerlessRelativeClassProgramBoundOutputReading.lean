import BMSConstructibleBridge.PowerlessFiniteProgramBoundOutputSyntax
import BMSConstructibleBridge.PowerlessRelativeClassTraceRelationReading

/-! # 同一绑定程序的真实输出与缺省输出读数

纯隶属 ℒ，背景原 Z₂。算子参数的 raw 环境允许额外域外元数据，
只要求 Class 输入／输出上的原算子同值。对同一有限历史、末状态和
存储图给出双向对应；不假定内部长度标准，也不假定无限输出图属于 Class。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassProgramBoundOutputReading

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
    (hOperator : ∀ x y : M, ψ.satisfies ((ξ.pushFree x.val).pushFree y.val) ↔
      φ.satisfies ((η.pushFree x).pushFree y)) (C ω w e t₀ t₁ t₂ a n k y : M) :
    PowerlessFiniteProgramBoundOutputSyntax.run_l φ η
      ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ C ω w e t₀ t₁ t₂ a n k y ↔
    PowerlessRelativeFiniteProgramBoundOutput.run_l ψ ξ B C.val ω.val w.val e.val
      t₀.val t₁.val t₂.val a.val n.val k.val y.val := by
  have hTrace (S D F : M) := PowerlessRelativeClassTraceRelationReading.reading_l (hBase := hBase)
    (PowerlessFiniteProgramStepSyntax.step_l φ η
      ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ C ω w e t₀ t₁ t₂)
    (PowerlessRelativeFiniteProgramStep.step_l ψ ξ B C.val ω.val w.val e.val
      t₀.val t₁.val t₂.val)
    (fun x z => (PowerlessRelativeClassProgramStepReading.step_l
      φ ψ η ξ hOperator C ω w e t₀ t₁ t₂ x z).symm) e a n S D F
  constructor
  · rintro ⟨S, D, F, s, E, g, hF, hs, hv, hy⟩
    exact ⟨S.val, D.val, F.val, s.val, E.val, g.val, D.property, F.property,
      (hTrace S D F).mp hF,
      (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) F n s).mp hs,
      (PowerlessRelativeClassProgramStepReading.valid_l (hBase := hBase) ω n E g s).mp hv,
      (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) g k y).mp hy⟩
  · rintro ⟨S, D, F, s, E, g, hDC, hFC, hF, hs, hv, hy⟩
    let S₀ : M := ⟨S, PowerlessRelativeClassFunctionAppend.adjoin_class_l
      hBase n.property n.property hF.1⟩
    let D₀ : M := ⟨D, hDC⟩
    let F₀ : M := ⟨F, hFC⟩
    let s₀ : M := ⟨s, (PowerlessRelativeClassValueCoordinates.value_l hBase F₀ hs).2⟩
    let E₀ : M := ⟨E, hv.2.2.2.1⟩
    let g₀ : M := ⟨g, hv.2.2.2.2.1⟩
    exact ⟨S₀, D₀, F₀, s₀, E₀, g₀, (hTrace S₀ D₀ F₀).mpr hF,
      (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) F₀ n s₀).mpr hs,
      (PowerlessRelativeClassProgramStepReading.valid_l (hBase := hBase) ω n E₀ g₀ s₀).mpr hv,
      (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) g₀ k y).mpr hy⟩

include hBase in
theorem run_class_l {Θ : SortContext ℒ} (ψ : Formula ℒ [] (.set :: .set :: Θ))
    (ξ : Env 𝒱 [] Θ) {C ω w e t₀ t₁ t₂ a n k y : SecondOrderQuotient.type_l hℳ}
    (hy : PowerlessRelativeFiniteProgramBoundOutput.run_l ψ ξ B C ω w e t₀ t₁ t₂ a n k y) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B y := by
  obtain ⟨_S, _D, _F, _s, _E, g, _hDC, _hFC, _hF, _hs, hv, hg⟩ := hy
  let g₀ : M := ⟨g, hv.2.2.2.2.1⟩
  exact (PowerlessRelativeClassValueCoordinates.value_l hBase g₀ hg).2

theorem output_l {Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (ψ : Formula ℒ [] (.set :: .set :: Θ))
    (η : Env 𝒩₀ [] Δ) (ξ : Env 𝒱 [] Θ)
    (hOperator : ∀ x y : M, ψ.satisfies ((ξ.pushFree x.val).pushFree y.val) ↔
      φ.satisfies ((η.pushFree x).pushFree y)) (C ω w e t₀ t₁ t₂ a n k y : M) :
    PowerlessFiniteProgramBoundOutputSyntax.output_l φ η
      ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ C ω w e t₀ t₁ t₂ a n k y ↔
    PowerlessRelativeFiniteProgramBoundOutput.output_l ψ ξ B C.val ω.val w.val e.val
      t₀.val t₁.val t₂.val a.val n.val k.val y.val := by
  have hSome : (∃ z, PowerlessRelativeFiniteProgramBoundOutput.run_l ψ ξ B C.val ω.val
      w.val e.val t₀.val t₁.val t₂.val a.val n.val k.val z) ↔
      ∃ z : M, PowerlessFiniteProgramBoundOutputSyntax.run_l φ η
        ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ C ω w e t₀ t₁ t₂ a n k z := by
    constructor
    · rintro ⟨z, hz⟩
      let z₀ : M := ⟨z, run_class_l (hBase := hBase) ψ ξ hz⟩
      exact ⟨z₀, (run_l φ ψ η ξ hOperator C ω w e t₀ t₁ t₂ a n k z₀).mpr hz⟩
    · rintro ⟨z, hz⟩
      exact ⟨z.val, (run_l φ ψ η ξ hOperator C ω w e t₀ t₁ t₂ a n k z).mp hz⟩
  have hEqual : y = ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ ↔ y.val = B :=
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hDisj := or_congr (run_l φ ψ η ξ hOperator C ω w e t₀ t₁ t₂ a n k y)
    (and_congr (not_congr hSome.symm) hEqual)
  exact ⟨fun h => ⟨y.property, hDisj.mp h⟩, fun h => hDisj.mpr h.2⟩

#print axioms run_l
#print axioms run_class_l
#print axioms output_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassProgramBoundOutputReading
