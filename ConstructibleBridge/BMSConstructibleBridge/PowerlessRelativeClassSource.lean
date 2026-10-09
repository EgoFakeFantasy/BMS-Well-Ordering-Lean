import BMSConstructibleBridge.PowerlessRelativeClassStructure
import BMSConstructibleBridge.PowerlessSourceRelationalIsomorphism

/-! # 实际 Class 结构与通用谓词结构的原公式认同

两个结构具有相同实际对象，但构造表达式不必定义相等。使用值相等
关系逐公式传输，显式核验两向全域性、等式和隶属；不抽取同构函数。
环境逐槽保留原对象。此接口只认同这两个呈现，不增加元素性或源公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSource

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessSourceClass.structure_l PowerlessSourceClass.type_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ z, SecondOrderQuotient.mem_l hℳ z B →
    ∀ t, SecondOrderQuotient.mem_l hℳ t z → SecondOrderQuotient.mem_l hℳ t B}
  {hP : ∃ z, PowerlessRelativeClassCorrespondence.member_l hℳ B z}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "𝒫" => PowerlessSourceClass.structure_l (ℳ := 𝒱)
  (PowerlessRelativeClassCorrespondence.member_l hℳ B) hP

def env_l {Γ Δ : SortContext ℒ} (η : Env 𝒫 Γ Δ) : Env 𝒩 Γ Δ where
  boundVal v := ⟨(η.boundVal v).val, (η.boundVal v).property⟩
  freeVal v := ⟨(η.freeVal v).val, (η.freeVal v).property⟩

theorem formula_l {Γ Δ : SortContext ℒ} (ψ : Formula ℒ Γ Δ) (η : Env 𝒫 Γ Δ) :
    ψ.satisfies (env_l (hBase := hBase) η) ↔ ψ.satisfies η := by
  let R : carrier_l 𝒩 → carrier_l 𝒫 → Prop := fun x y => x.val = y.val
  have hTotal : ∀ x, ∃ y, R x y := fun x => ⟨⟨x.val, x.property⟩, rfl⟩
  have hOnto : ∀ y, ∃ x, R x y := fun y => ⟨⟨y.val, y.property⟩, rfl⟩
  have hEq : ∀ {x z y w}, R x y → R z w → (x = z ↔ y = w) := by
    intro x z y w hxy hzw
    constructor
    · intro h
      exact Subtype.ext (hxy.symm.trans ((congrArg Subtype.val h).trans hzw))
    · intro h
      exact Subtype.ext (hxy.trans ((congrArg Subtype.val h).trans hzw.symm))
  have hMem : ∀ {x z y w}, R x y → R z w →
      (member_l 𝒩 x z ↔ member_l 𝒫 y w) := by
    intro x z y w hxy hzw
    change SecondOrderQuotient.mem_l hℳ x.val z.val ↔ SecondOrderQuotient.mem_l hℳ y.val w.val
    rw [hxy, hzw]
  exact PowerlessSourceRelationalIsomorphism.formula_l R hTotal hOnto hEq hMem
    ψ (env_l (hBase := hBase) η) η ⟨fun _ => rfl, fun _ => rfl⟩

#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSource
