import BMSConstructibleBridge.PowerlessFiniteProgramNumberEvaluationSyntax
import BMSConstructibleBridge.PowerlessRelativeClassProgramEvaluationReading
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramNumberEvaluation

/-! # 原 U 枚举及同一数码求值的类内读数

纯隶属 ℒ，背景原 Z₂。只读取同一个 U 的图，由实际图取得解码
程序 p 的 Class 资格，然后使用完整求值对应。既不换数码枚举，
也不从逐点输出资格推出整张图的资格；后者仍须原分离构造。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassProgramNumberEvaluationReading

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

theorem number_l {Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (ψ : Formula ℒ [] (.set :: .set :: Θ))
    (η : Env 𝒩₀ [] Δ) (ξ : Env 𝒱 [] Θ)
    (hOperator : ∀ x y : M, ψ.satisfies ((ξ.pushFree x.val).pushFree y.val) ↔
      φ.satisfies ((η.pushFree x).pushFree y)) (C ω Q e t₀ t₁ t₂ a U n y : M) :
    PowerlessFiniteProgramNumberEvaluationSyntax.number_l φ η
      ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ C ω Q e t₀ t₁ t₂ a U n y ↔
    PowerlessRelativeFiniteProgramNumberEvaluation.number_l ψ ξ B C.val ω.val Q.val e.val
      t₀.val t₁.val t₂.val a.val U.val n.val y.val := by
  constructor
  · rintro ⟨p, hp, hy⟩
    exact ⟨p.val, (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) U n p).mp hp,
      (PowerlessRelativeClassProgramEvaluationReading.matrix_l false
        φ ψ η ξ hOperator C ω Q e t₀ t₁ t₂ a p y).mp hy⟩
  · rintro ⟨p, hp, hy⟩
    let p₀ : M := ⟨p, (PowerlessRelativeClassValueCoordinates.value_l hBase U hp).2⟩
    exact ⟨p₀, (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) U n p₀).mpr hp,
      (PowerlessRelativeClassProgramEvaluationReading.matrix_l false
        φ ψ η ξ hOperator C ω Q e t₀ t₁ t₂ a p₀ y).mpr hy⟩

include hBase in
theorem number_class_l {Θ : SortContext ℒ}
    (ψ : Formula ℒ [] (.set :: .set :: Θ)) (ξ : Env 𝒱 [] Θ)
    {C ω Q e t₀ t₁ t₂ a U n y : SecondOrderQuotient.type_l hℳ}
    (hy : PowerlessRelativeFiniteProgramNumberEvaluation.number_l ψ ξ B C ω Q e t₀ t₁ t₂ a U n y) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B y := by
  obtain ⟨_p, _hp, hy⟩ := hy
  exact PowerlessRelativeClassProgramEvaluationReading.matrix_class_l (hBase := hBase) false ψ ξ hy

#print axioms number_l
#print axioms number_class_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassProgramNumberEvaluationReading
