import BMSConstructibleBridge.PowerlessRelativeClassSource
import BMSConstructibleBridge.PowerlessSourceClassInclusion
import BMSConstructibleBridge.PowerlessWholeCollapseTruth
import BMSConstructibleBridge.PowerlessSourceFreeBinding

/-! # 同一类请求及原全坍缩的有限公式反射

原 Class 有限请求先给虚拟域包含上的真值对应，再沿同一 project
传到实际 T。原赋值的每槽有显式对应，不抽取同构或量词见证函数。
自由参数可以全部绑定，以消费同一实际程序空自由上下文的请求闭包。
这是语义装配接口，实际程序的请求闭包须由已有构造规格取得。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassWholeCollapseReflection

open Logic FirstOrder ThirdOrderSemantics
open PowerlessDefinableMembershipIsomorphism (image_l project_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l
  PowerlessSourceClass.structure_l PowerlessSourceClass.type_l
  PowerlessMemberStructure.structure_l PowerlessMemberStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
    ∀ z, SecondOrderQuotient.mem_l hℳ z x → SecondOrderQuotient.mem_l hℳ z B}
  {hP : ∃ x, PowerlessRelativeClassCorrespondence.member_l hℳ B x}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒩₀" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "𝒫₀" => PowerlessSourceClass.structure_l (ℳ := 𝒱)
  (PowerlessRelativeClassCorrespondence.member_l hℳ B) hP

/-- 原绑定值的 project 对应足以建立 Class 与实际成员结构的真值对应。 -/
theorem formula_l {Δ Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (C T H : Raw)
    (hIso : PowerlessDefinableWholeCollapse.isomorphism_l φ η C T H)
    {hI : ∃ x, image_l φ η C x} {hT : ∃ x, SecondOrderQuotient.mem_l hℳ x T}
    (hIP : ∀ x, image_l φ η C x → PowerlessRelativeClassCorrespondence.member_l hℳ B x)
    (ψ : Formula ℒ Γ []) (ξ : Env 𝒩₀ Γ [])
    (ζ : Env (PowerlessMemberStructure.structure_l (ℳ := 𝒱) T hT) Γ [])
    (hProject : ∀ v : Variable Γ .set,
      project_l φ η C H (ξ.boundVal v).val (ζ.boundVal v).val)
    (hCapture : PowerlessSourcePredicateRequests.closed_l
      (PowerlessSourceRequests.requests_m .truth ψ) (Env.empty (M := 𝒫₀))
      (fun x => image_l φ η C x.val)) : ψ.satisfies ξ ↔ ψ.satisfies ζ := by
  have hImage (v : Variable Γ .set) : image_l φ η C (ξ.boundVal v).val := by
    obtain ⟨n, hn, hnx, _⟩ := hProject v
    exact ⟨n, hn, hnx⟩
  let ξI : Env (PowerlessSourceClass.structure_l (ℳ := 𝒱) (image_l φ η C) hI) Γ [] :=
    { boundVal := fun {s} v => match s with | .set => ⟨(ξ.boundVal v).val, hImage v⟩
      freeVal := fun v => nomatch v }
  have hξ : PowerlessRelativeClassSource.env_l (hBase := hBase)
      (PowerlessSourceClassInclusion.env_l (hP := hP) hIP ξI) = ξ := by
    apply Env.ext
    · intro s v
      cases s
      exact Subtype.ext rfl
    · intro _ v; nomatch v
  have hFree : PowerlessSourceClass.free_l
      (PowerlessSourceClassInclusion.env_l (hP := hP) hIP ξI) = Env.empty := by
    apply Env.ext <;> intro _ v <;> nomatch v
  have hSource := PowerlessRelativeClassSource.formula_l (hBase := hBase) ψ
    (PowerlessSourceClassInclusion.env_l (hP := hP) hIP ξI)
  rw [hξ] at hSource
  have hIncluded := PowerlessSourceClassInclusion.formula_l (hP := hP) hIP ψ ξI
    (by simpa only [hFree] using hCapture)
  have hTarget := PowerlessWholeCollapseTruth.formula_l φ η C T H hIso ψ ξI ζ
    ⟨fun v => hProject v, fun v => nomatch v⟩
  exact hSource.trans (hIncluded.trans hTarget)

/-- 原自由参数按原次序绑定，请求闭包不随实际输入值更换。 -/
theorem open_formula_l {Δ Θ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (C T H : Raw)
    (hIso : PowerlessDefinableWholeCollapse.isomorphism_l φ η C T H)
    {hI : ∃ x, image_l φ η C x} {hT : ∃ x, SecondOrderQuotient.mem_l hℳ x T}
    (hIP : ∀ x, image_l φ η C x → PowerlessRelativeClassCorrespondence.member_l hℳ B x)
    (ψ : Formula ℒ [] Θ) (ξ : Env 𝒩₀ [] Θ)
    (ζ : Env (PowerlessMemberStructure.structure_l (ℳ := 𝒱) T hT) [] Θ)
    (hProject : ∀ v : Variable Θ .set,
      project_l φ η C H (ξ.freeVal v).val (ζ.freeVal v).val)
    (hCapture : PowerlessSourcePredicateRequests.closed_l
      (PowerlessSourceRequests.requests_m .truth (PowerlessSourceFreeBinding.formula_m ψ))
      (Env.empty (M := 𝒫₀)) (fun x => image_l φ η C x.val)) :
    ψ.satisfies ξ ↔ ψ.satisfies ζ :=
  (PowerlessSourceFreeBinding.formula_l ψ ξ).symm.trans
    ((formula_l (hI := hI) φ η C T H hIso hIP
      (PowerlessSourceFreeBinding.formula_m ψ) (PowerlessSourceFreeBinding.env_l ξ)
      (PowerlessSourceFreeBinding.env_l ζ) hProject hCapture).trans
        (PowerlessSourceFreeBinding.formula_l ψ ζ))

#print axioms formula_l
#print axioms open_formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassWholeCollapseReflection
