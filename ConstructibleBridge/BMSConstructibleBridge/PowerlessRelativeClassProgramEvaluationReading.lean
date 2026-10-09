import BMSConstructibleBridge.PowerlessFiniteProgramEvaluationSyntax
import BMSConstructibleBridge.PowerlessRelativeClassProgramBoundOutputReading
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramEvaluation

/-! # 同一全程序码的完整求值读数

纯隶属 ℒ，背景原 Z₂。类内有序对编码的两个坐标及内部长度从
原 raw 正文取得资格，原函数图、程序与输出保持同一。真实 run 和
含 B 缺省的 output 均对应全部原候选，不要求算子是 Δ₀。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassProgramEvaluationReading

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

include hBase in
private theorem coordinates_l (p : M) {w k : SecondOrderQuotient.type_l hℳ}
    (hp : ordered_l (ℳ := 𝒱) w k p.val) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B w ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ B k := by
  obtain ⟨s, t, _hs, ht, hPair⟩ := hp
  have htClass := PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase p.property
    ((hPair t).mpr (Or.inr rfl))
  exact ⟨PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase htClass ((ht w).mpr (Or.inl rfl)),
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase htClass ((ht k).mpr (Or.inr rfl))⟩

theorem matrix_l {Δ Θ : SortContext ℒ} (actual : Bool)
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (ψ : Formula ℒ [] (.set :: .set :: Θ))
    (η : Env 𝒩₀ [] Δ) (ξ : Env 𝒱 [] Θ)
    (hOperator : ∀ x y : M, ψ.satisfies ((ξ.pushFree x.val).pushFree y.val) ↔
      φ.satisfies ((η.pushFree x).pushFree y)) (C ω Q e t₀ t₁ t₂ a p y : M) :
    PowerlessFiniteProgramEvaluationSyntax.matrix_l actual φ η
      ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ C ω Q e t₀ t₁ t₂ a p y ↔
    PowerlessRelativeFiniteProgramEvaluation.matrix_l actual ψ ξ B C.val ω.val Q.val e.val
      t₀.val t₁.val t₂.val a.val p.val y.val := by
  have hRead (w k n : M) :
      (if actual then PowerlessFiniteProgramBoundOutputSyntax.run_l φ η
        ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ C ω w e t₀ t₁ t₂ a n k y
       else PowerlessFiniteProgramBoundOutputSyntax.output_l φ η
        ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ C ω w e t₀ t₁ t₂ a n k y) ↔
      (if actual then PowerlessRelativeFiniteProgramBoundOutput.run_l ψ ξ B C.val ω.val w.val
        e.val t₀.val t₁.val t₂.val a.val n.val k.val y.val
       else PowerlessRelativeFiniteProgramBoundOutput.output_l ψ ξ B C.val ω.val w.val
        e.val t₀.val t₁.val t₂.val a.val n.val k.val y.val) := by
    cases actual
    · exact PowerlessRelativeClassProgramBoundOutputReading.output_l
        φ ψ η ξ hOperator C ω w e t₀ t₁ t₂ a n k y
    · exact PowerlessRelativeClassProgramBoundOutputReading.run_l
        φ ψ η ξ hOperator C ω w e t₀ t₁ t₂ a n k y
  constructor
  · rintro ⟨w, k, n, hp, hk, hn, hw, hy⟩
    exact ⟨w.val, k.val, n.val,
      (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) w k p).mp hp, hk, hn,
      (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) w n Q).mp hw,
      (hRead w k n).mp hy⟩
  · rintro ⟨w, k, n, hp, hk, hn, hw, hy⟩
    have hWK := coordinates_l (hBase := hBase) p hp
    let w₀ : M := ⟨w, hWK.1⟩
    let k₀ : M := ⟨k, hWK.2⟩
    let n₀ : M := ⟨n, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property hn⟩
    exact ⟨w₀, k₀, n₀,
      (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) w₀ k₀ p).mpr hp, hk, hn,
      (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) w₀ n₀ Q).mpr hw,
      (hRead w₀ k₀ n₀).mpr hy⟩

include hBase in
theorem matrix_class_l {Θ : SortContext ℒ} (actual : Bool)
    (ψ : Formula ℒ [] (.set :: .set :: Θ)) (ξ : Env 𝒱 [] Θ)
    {C ω Q e t₀ t₁ t₂ a p y : SecondOrderQuotient.type_l hℳ}
    (hy : PowerlessRelativeFiniteProgramEvaluation.matrix_l actual ψ ξ B C ω Q e t₀ t₁ t₂ a p y) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B y := by
  obtain ⟨_w, _k, _n, _hp, _hk, _hn, _hw, hy⟩ := hy
  cases actual
  · exact hy.1
  · exact PowerlessRelativeClassProgramBoundOutputReading.run_class_l (hBase := hBase) ψ ξ hy

#print axioms matrix_l
#print axioms matrix_class_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassProgramEvaluationReading
