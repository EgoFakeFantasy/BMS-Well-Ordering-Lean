import BMSConstructibleBridge.PowerlessClassWholeCollapseReflection
import BMSConstructibleBridge.PowerlessRelativeClassReflectedSeparation

/-! # 同一原全坍缩反射产生实际 Class 分离见证

固定传递种子覆盖输入集合及原参数，同一 project 因而固定全部实际
输入成员。原公式的自由槽全部绑定为同一个有限请求，不为每个输入
重建请求族。类／T 真值对应在证明内取得，然后使用已证反射分离。
同构、TClass、种子固定及实际请求闭包仍须由原程序构造层提供。
这里没有把任意 raw 定义默认认同为同一公式的 Class 真值。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassWholeCollapseSeparation

open Logic FirstOrder ThirdOrderSemantics
open PowerlessDefinableMembershipIsomorphism (image_l project_l)
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l
  PowerlessSourceClass.structure_l PowerlessSourceClass.type_l
  PowerlessMemberStructure.structure_l PowerlessMemberStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B}
  {hP : ∃ x, PowerlessRelativeClassCorrespondence.member_l hℳ B x}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒩₀" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "𝒫₀" => PowerlessSourceClass.structure_l (ℳ := 𝒱)
  (PowerlessRelativeClassCorrespondence.member_l hℳ B) hP

/-- 真值对应和分离见证都由同一请求及同一 project 取得。 -/
theorem exists_l {Δ Θ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (C T H D : Raw)
    (ψ : Formula ℒ [] (.set :: Θ)) (σ : Env 𝒩₀ [] Θ)
    (X : PowerlessRelativeClassStructure.type_l hℳ B)
    (hIso : PowerlessDefinableWholeCollapse.isomorphism_l φ η C T H)
    (hT : PowerlessRelativeClassCorrespondence.member_l hℳ B T)
    (hIP : ∀ x, image_l φ η C x → PowerlessRelativeClassCorrespondence.member_l hℳ B x)
    (hD : ∀ x, mem_l hℳ x D → ∀ z, mem_l hℳ z x → mem_l hℳ z D)
    (hFixed : ∀ x, mem_l hℳ x D → mem_l hℳ x T ∧ project_l φ η C H x x)
    (hXD : mem_l hℳ X.val D)
    (hParams : ∀ v : Variable Θ .set, mem_l hℳ (σ.freeVal v).val D)
    (hCapture : PowerlessSourcePredicateRequests.closed_l
      (PowerlessSourceRequests.requests_m .truth (PowerlessSourceFreeBinding.formula_m ψ))
      (Env.empty (M := 𝒫₀)) (fun x => image_l φ η C x.val)) :
    ∃ Y : PowerlessRelativeClassStructure.type_l hℳ B,
      ∀ x : PowerlessRelativeClassStructure.type_l hℳ B,
        mem_l hℳ x.val Y.val ↔ mem_l hℳ x.val X.val ∧ ψ.satisfies (σ.pushFree x) := by
  have hXT := (hFixed X.val hXD).1
  have hParameterT (v : Variable Θ .set) := (hFixed (σ.freeVal v).val (hParams v)).1
  have hCover (x : PowerlessRelativeClassStructure.type_l hℳ B)
      (hx : mem_l hℳ x.val X.val) := (hFixed x.val (hD X.val hXD x.val hx)).1
  have hNonemptyI : ∃ x, image_l φ η C x := by
    obtain ⟨n, hn, hnx, _⟩ := (hFixed X.val hXD).2
    exact ⟨X.val, n, hn, hnx⟩
  apply PowerlessRelativeClassReflectedSeparation.class_exists_l ψ σ X ⟨T, hT⟩
    hXT hCover hParameterT
  intro x hx
  let ζ := PowerlessRelativeClassReflectedSeparation.member_env_l σ T ⟨X.val, hXT⟩ hParameterT
  exact PowerlessClassWholeCollapseReflection.open_formula_l
    (hBase := hBase) (hP := hP) (hI := hNonemptyI) φ η C T H hIso hIP ψ
    (σ.pushFree x) (ζ.pushFree (sort := SetTheory.SetSort.set) ⟨x.val, hCover x hx⟩)
    (fun v => by
      cases v with
      | here => exact (hFixed x.val (hD X.val hXD x.val hx)).2
      | there v => exact (hFixed (σ.freeVal v).val (hParams v)).2) hCapture

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassWholeCollapseSeparation
