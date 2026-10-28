import BMSConstructibleBridge.PowerlessSourcePredicateRequests
import BMSConstructibleBridge.PowerlessSourceRelationalIsomorphism

/-! # 任意谓词子域包含与原请求反射

虚拟域不必是集合。原请求反射先在类结构中的谓词子域完成，再用
显式双重子类型的关系对应读回环境中的同一个虚拟域，不抽取函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceClassInclusion

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  PowerlessSourceClass.structure_l PowerlessSourceClass.type_l

universe u

variable {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  {I P : carrier_l 𝒱 → Prop} {hI : ∃ x, I x} {hP : ∃ x, P x}

local notation "𝒩" => PowerlessSourceClass.structure_l (ℳ := 𝒱) I hI
local notation "ℳ₀" => PowerlessSourceClass.structure_l (ℳ := 𝒱) P hP

def inclusion_l (hIP : ∀ x, I x → P x) (x : PowerlessSourceClass.type_l (ℳ := 𝒱) I) :
    PowerlessSourceClass.type_l (ℳ := 𝒱) P := ⟨x.val, hIP x.val x.property⟩

def env_l {Γ Δ : SortContext ℒ} (hIP : ∀ x, I x → P x) (η : Env 𝒩 Γ Δ) : Env ℳ₀ Γ Δ where
  boundVal v := inclusion_l hIP (η.boundVal v)
  freeVal v := inclusion_l hIP (η.freeVal v)

private theorem nonempty_l (hIP : ∀ x, I x → P x) (hi : ∃ x, I x) :
    ∃ x : PowerlessSourceClass.type_l (ℳ := 𝒱) P, I x.val :=
  hi.elim fun x hx => ⟨⟨x, hIP x hx⟩, hx⟩

private def nested_l {Γ Δ : SortContext ℒ} (hIP : ∀ x, I x → P x)
    (η : Env 𝒩 Γ Δ) :
    Env (PowerlessSourceClass.structure_l (ℳ := ℳ₀) (fun x => I x.val) (nonempty_l hIP hI)) Γ Δ where
  boundVal v := ⟨inclusion_l hIP (η.boundVal v), (η.boundVal v).property⟩
  freeVal v := ⟨inclusion_l hIP (η.freeVal v), (η.freeVal v).property⟩

/-- 原请求闭包给实际谓词包含上的逐公式反射，不增加原见证存在性。 -/
theorem formula_l {Γ Δ : SortContext ℒ} (hIP : ∀ x, I x → P x)
    (φ : Formula ℒ Γ Δ) (η : Env 𝒩 Γ Δ)
    (h : PowerlessSourcePredicateRequests.closed_l (PowerlessSourceRequests.requests_m .truth φ)
      (PowerlessSourceClass.free_l (env_l (hP := hP) hIP η)) (fun x => I x.val)) :
    φ.satisfies (env_l (hP := hP) hIP η) ↔ φ.satisfies η := by
  let ℳ₁ := PowerlessSourceClass.structure_l (ℳ := ℳ₀) (fun x => I x.val) (nonempty_l hIP hI)
  let R : carrier_l ℳ₁ → carrier_l 𝒩 → Prop := fun x y => x.val.val = y.val
  have hη : PowerlessSourceClass.env_l (nested_l (hP := hP) hIP η) =
      env_l (hP := hP) hIP η := by
    apply Env.ext <;> intro _ _ <;> rfl
  have h₀ := PowerlessSourcePredicateRequests.formula_l φ (nested_l (hP := hP) hIP η)
    (by simpa only [hη] using h)
  have hTotal : ∀ x, ∃ y, R x y := fun x => ⟨⟨x.val.val, x.property⟩, rfl⟩
  have hOnto : ∀ y, ∃ x, R x y := fun y => ⟨⟨⟨y.val, hIP y.val y.property⟩, y.property⟩, rfl⟩
  have hEq : ∀ {x z y w}, R x y → R z w → (x = z ↔ y = w) := by
    intro x z y w hxy hzw
    constructor
    · intro hxz
      subst z
      exact Subtype.ext (hxy.symm.trans hzw)
    · intro hyw
      subst w
      exact Subtype.ext (Subtype.ext (hxy.trans hzw.symm))
  have hMem : ∀ {x z y w}, R x y → R z w → (member_l ℳ₁ x z ↔ member_l 𝒩 y w) := by
    intro x z y w hxy hzw
    change member_l 𝒱 x.val.val z.val.val ↔ member_l 𝒱 y.val w.val
    rw [hxy, hzw]
  have hRel : PowerlessSourceRelationalIsomorphism.related_l R (nested_l (hP := hP) hIP η) η :=
    ⟨fun _ => rfl, fun _ => rfl⟩
  have h₁ := PowerlessSourceRelationalIsomorphism.formula_l R hTotal hOnto hEq hMem
    φ (nested_l (hP := hP) hIP η) η hRel
  rw [hη] at h₀
  exact h₀.trans h₁

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceClassInclusion
