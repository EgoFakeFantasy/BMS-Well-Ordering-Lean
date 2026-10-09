import BMSConstructibleBridge.PowerlessDefinableWholeCollapse
import BMSConstructibleBridge.PowerlessSourceRelationalIsomorphism
import BMSConstructibleBridge.PowerlessMemberStructure

/-! # 原全部虚拟输出与同一实际坍缩值域的公式传输

载体分别是原求值全像的谓词子类型和实际 T 的成员。使用原 project
关系的双向全域性、单值、反向单射及隶属对应；不另收集全像，不抽取
Type 同构函数，也不假定 T/H 属于 Class。原公式及原参数环境保持。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessWholeCollapseTruth

open Logic FirstOrder ThirdOrderSemantics
open PowerlessDefinableMembershipIsomorphism (image_l project_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessSourceClass.structure_l PowerlessSourceClass.type_l
  PowerlessMemberStructure.structure_l PowerlessMemberStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "ε" => SecondOrderQuotient.mem_l hℳ

def relation_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (C T H : Raw)
    (x : PowerlessSourceClass.type_l (ℳ := 𝒱) (image_l φ η C))
    (y : PowerlessMemberStructure.type_l (ℳ := 𝒱) T) : Prop :=
  project_l φ η C H x.val y.val

theorem nonempty_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (C T H : Raw)
    (hIso : PowerlessDefinableWholeCollapse.isomorphism_l φ η C T H)
    (hI : ∃ x, image_l φ η C x) : ∃ y, ε y T := by
  obtain ⟨x, hx⟩ := hI
  obtain ⟨y, hy, _⟩ := hIso.1 x hx
  exact ⟨y, hy⟩

/-- 将通用关系传输实例化到原 project 与实际 T，而非任意另选同构。 -/
theorem formula_l {Δ Γ Θ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (C T H : Raw)
    (hIso : PowerlessDefinableWholeCollapse.isomorphism_l φ η C T H)
    {hI : ∃ x, image_l φ η C x} {hT : ∃ y, ε y T}
    (ψ : Formula ℒ Γ Θ)
    (ξ : Env (PowerlessSourceClass.structure_l (ℳ := 𝒱) (image_l φ η C) hI) Γ Θ)
    (ζ : Env (PowerlessMemberStructure.structure_l (ℳ := 𝒱) T hT) Γ Θ)
    (h : PowerlessSourceRelationalIsomorphism.related_l (relation_l φ η C T H) ξ ζ) :
    ψ.satisfies ξ ↔ ψ.satisfies ζ := by
  let R := relation_l φ η C T H
  have hTotal : ∀ x, ∃ y, R x y := by
    intro x
    obtain ⟨y, hy, hxy⟩ := hIso.1 x.val x.property
    exact ⟨⟨y, hy⟩, hxy⟩
  have hOnto : ∀ y, ∃ x, R x y := by
    intro y
    obtain ⟨x, hx⟩ := hIso.2.2.2.2 y.val y.property
    obtain ⟨n, hn, hnx, hny⟩ := hx
    exact ⟨⟨x, n, hn, hnx⟩, n, hn, hnx, hny⟩
  have hEq : ∀ {x z y w}, R x y → R z w → (x = z ↔ y = w) := by
    intro x z y w hxy hzw
    constructor
    · intro hxz
      subst z
      exact Subtype.ext (hIso.2.2.1 x.val y.val w.val hxy hzw)
    · intro hyw
      subst w
      exact Subtype.ext (hIso.2.1 x.val z.val y.val hxy hzw)
  have hMem : ∀ {x z y w}, R x y → R z w →
      (member_l (PowerlessSourceClass.structure_l (ℳ := 𝒱) (image_l φ η C) hI) x z ↔
        member_l (PowerlessMemberStructure.structure_l (ℳ := 𝒱) T hT) y w) := by
    intro x z y w hxy hzw
    exact hIso.2.2.2.1 x.val z.val y.val w.val hxy hzw
  exact PowerlessSourceRelationalIsomorphism.formula_l R hTotal hOnto hEq hMem ψ ξ ζ h

#print axioms nonempty_l
#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessWholeCollapseTruth
