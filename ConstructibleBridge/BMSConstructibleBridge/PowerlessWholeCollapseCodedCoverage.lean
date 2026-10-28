import BMSConstructibleBridge.PowerlessRelativeClassCodedCoverage
import BMSConstructibleBridge.PowerlessSourceClassInclusion
import BMSConstructibleBridge.PowerlessRelativeClassSource
import BMSConstructibleBridge.PowerlessWholeCollapseClosure
import BMSConstructibleBridge.PowerlessRelativeCodedHistoryCollapseReading

/-! # 实际 Class 覆盖沿同一全像坍缩传到目标

原覆盖存在式先由实际 Class 定理成立，再由该原式的请求闭包反射到
虚拟全像。完整 AST 沿同一 project 传到 MemberT；只有此后才使用
真实传递性和操作闭包读回全部 raw 资格。没有首 Ω／W 或 ClassT 假设。
请求闭包和种子固定是此辅助接口的输入，实际程序必须在下一模块消去。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessWholeCollapseCodedCoverage

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessDefinableMembershipIsomorphism (image_l project_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessSourceClass.structure_l PowerlessSourceClass.type_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l
  PowerlessMemberStructure.structure_l PowerlessMemberStructure.type_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "ε" => SecondOrderQuotient.mem_l hℳ

theorem packet_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ) (C T H B ω : Raw)
    (hBase : ∀ z, ε z B → ∀ t, ε t z → ε t B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hIso : PowerlessDefinableWholeCollapse.isomorphism_l φ η C T H)
    (hTrans : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) T)
    (hIP : ∀ x, image_l φ η C x → PowerlessRelativeClassCorrespondence.member_l hℳ B x)
    (hClosed : PowerlessWholeCollapseClosure.closed_l φ η C)
    (hBI : image_l φ η C B) (hωI : image_l φ η C ω)
    (hBT : ε B T) (hωT : ε ω T)
    (hFixedB : project_l φ η C H B B) (hFixedω : project_l φ η C H ω ω)
    (hRequests : PowerlessSourcePredicateRequests.closed_l
      (PowerlessSourceRequests.requests_m .truth (PowerlessRelativeFiniteHullCodedCoverage.exists_m []))
      (Env.empty : Env (PowerlessSourceClass.structure_l (ℳ := 𝒱)
        (PowerlessRelativeClassCorrespondence.member_l hℳ B)
        ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩) [] [])
      (fun x => image_l φ η C x.val)) :
    ∀ x, ε x T → PowerlessRelativeCodedHistoryCollapseReading.packet_l T B K.omega x := by
  let I := image_l φ η C
  have hI : ∃ z, I z := ⟨B, hBI⟩
  have hClass : ∃ z, PowerlessRelativeClassCorrespondence.member_l hℳ B z :=
    ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩
  have hT : ∃ z, ε z T := ⟨B, hBT⟩
  let 𝒩 := PowerlessSourceClass.structure_l (ℳ := 𝒱) I hI
  let 𝒯 := PowerlessMemberStructure.structure_l (ℳ := 𝒱) T hT
  let B₀ : PowerlessSourceClass.type_l (ℳ := 𝒱) I := ⟨B, hBI⟩
  let ω₀ : PowerlessSourceClass.type_l (ℳ := 𝒱) I := ⟨ω, hωI⟩
  let B₁ : PowerlessMemberStructure.type_l (ℳ := 𝒱) T := ⟨B, hBT⟩
  let ω₁ : PowerlessMemberStructure.type_l (ℳ := 𝒱) T := ⟨ω, hωT⟩
  have hTargetClosed := PowerlessWholeCollapseClosure.target_l φ η C T H hIso hTrans hClosed
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  intro x hx
  obtain ⟨z, hzx⟩ := hIso.2.2.2.2 x hx
  have hzI : I z := by
    obtain ⟨n, hn, hnz, _⟩ := hzx
    exact ⟨n, hn, hnz⟩
  let z₀ : PowerlessSourceClass.type_l (ℳ := 𝒱) I := ⟨z, hzI⟩
  let x₁ : PowerlessMemberStructure.type_l (ℳ := 𝒱) T := ⟨x, hx⟩
  let ξ : Env 𝒩 [.set, .set, .set] [] := (Env.empty : Env 𝒩 [] [])
    |>.pushBound (sort := SetTheory.SetSort.set) B₀
    |>.pushBound (sort := SetTheory.SetSort.set) ω₀
    |>.pushBound (sort := SetTheory.SetSort.set) z₀
  let ζ : Env 𝒯 [.set, .set, .set] [] := (Env.empty : Env 𝒯 [] [])
    |>.pushBound (sort := SetTheory.SetSort.set) B₁
    |>.pushBound (sort := SetTheory.SetSort.set) ω₁
    |>.pushBound (sort := SetTheory.SetSort.set) x₁
  have hFree : PowerlessSourceClass.free_l
      (PowerlessSourceClassInclusion.env_l (hP := hClass) hIP ξ) = Env.empty := by
    apply Env.ext <;> intro _ v <;> nomatch v
  have hCover := PowerlessRelativeClassCodedCoverage.exists_l (hBase := hBase) K
    ⟨ω, hIP ω hωI⟩ ⟨z, hIP z hzI⟩ hω
  let ξ₀ := PowerlessSourceClassInclusion.env_l (hP := hClass) hIP ξ
  have hOutside₀ := (PowerlessRelativeFiniteHullCodedCoverage.exists_formula_l
    (PowerlessRelativeClassStructure.ext_l hℳ B hBase)
    (PowerlessRelativeClassSource.env_l (hBase := hBase) ξ₀)).mpr hCover
  have hOutside := (PowerlessRelativeClassSource.formula_l (hBase := hBase)
    (PowerlessRelativeFiniteHullCodedCoverage.exists_m []) ξ₀).mp hOutside₀
  have hInside := (PowerlessSourceClassInclusion.formula_l (hP := hClass) hIP
    (PowerlessRelativeFiniteHullCodedCoverage.exists_m []) ξ
    (by simpa only [hFree] using hRequests)).mp hOutside
  have hRelated : PowerlessSourceRelationalIsomorphism.related_l
      (PowerlessWholeCollapseTruth.relation_l φ η C T H) ξ ζ := by
    constructor
    · intro v
      cases v with
      | here => exact hzx
      | there v => cases v with
        | here => exact hFixedω
        | there v => cases v with
          | here => exact hFixedB
          | there v => nomatch v
    · intro v
      nomatch v
  have hTarget := (PowerlessWholeCollapseTruth.formula_l φ η C T H hIso
    (PowerlessRelativeFiniteHullCodedCoverage.exists_m []) ξ ζ hRelated).mp hInside
  have hPoint := (PowerlessRelativeFiniteHullCodedCoverage.exists_formula_l
    (PowerlessRelativeCodedHistoryCollapseReading.ext_l hT hTrans) ζ).mp hTarget
  obtain ⟨a, y, A, U, D, f, e, t₁, t₂, t₃, t₄, P, N, F, V, Q, G, h⟩ := hPoint
  have hRaw := PowerlessMemberCodedHistoryReading.point_l (hW₀ := hT) K
    hTrans hTargetClosed B₁ ω₁ x₁ a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G hω h
  exact ⟨a, y, A, U, D, f, e, t₁, t₂, t₃, t₄, P, N, F, V, Q, G, hωEq ▸ hRaw⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessWholeCollapseCodedCoverage
