import BMSConstructibleBridge.PowerlessRelativeClassRelation

/-! # 类内有界函数关系的实际集合图

全域单值性针对实际类域给定，不是宿主函数。关系图由原 Δ₀ 图存在模式
构造，再以 Kuratowski 坐标唯一性验证集合函数及逐值对应。没有 Type 选择。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFunctionRelation

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem exists_l {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) (η : Env (structure_l hℳ B hBase) [] Δ)
    (X Y : type_l hℳ B)
    (hTotal : ∀ x : type_l hℳ B, mem_l hℳ x.val X.val → ∃! y : type_l hℳ B,
      mem_l hℳ y.val Y.val ∧ φ.satisfies ((η.pushFree y).pushFree x)) :
    ∃ f : type_l hℳ B, map_l (ℳ := structure_l hℳ B hBase) f X Y ∧
      ∀ x y : type_l hℳ B, value_l (ℳ := structure_l hℳ B hBase) f x y ↔
        mem_l hℳ x.val X.val ∧ mem_l hℳ y.val Y.val ∧ φ.satisfies ((η.pushFree y).pushFree x) := by
  obtain ⟨f, hf⟩ := PowerlessRelativeClassRelation.exists_l hφ η X Y
  have hValue (x y : type_l hℳ B) : value_l (ℳ := structure_l hℳ B hBase) f x y ↔
      mem_l hℳ x.val X.val ∧ mem_l hℳ y.val Y.val ∧ φ.satisfies ((η.pushFree y).pushFree x) := by
    constructor
    · rintro ⟨p, hp, hxy⟩
      obtain ⟨a, b, ha, hb, hab, hφab⟩ := (hf p).mp hp
      have hEq := (SecondOrderPairObjects.ordered_eq_l hℳ
        ((PowerlessRelativeClassFunctionAbsolute.ordered_l x y p).mp hxy)
        ((PowerlessRelativeClassFunctionAbsolute.ordered_l a b p).mp hab)).mp rfl
      have hxa : x = a := Subtype.ext hEq.1
      have hyb : y = b := Subtype.ext hEq.2
      simpa only [hxa, hyb] using And.intro ha (And.intro hb hφab)
    · rintro ⟨hx, hy, hφxy⟩
      obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ x.val y.val
      let p' : type_l hℳ B := ⟨p, PowerlessRelativeClassPair.ordered_l hℳ hBase x.property y.property hp⟩
      have hp' := (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) x y p').mpr hp
      exact ⟨p', (hf p').mpr ⟨x, y, hx, hy, hp', hφxy⟩, hp'⟩
  refine ⟨f, ⟨?_, ?_⟩, hValue⟩
  · intro p hp
    obtain ⟨x, y, hx, hy, hxy, _⟩ := (hf p).mp hp
    exact ⟨x, y, hx, hy, hxy⟩
  · intro x hx
    obtain ⟨y, ⟨hy, hφxy⟩, hUnique⟩ := hTotal x hx
    refine ⟨y, ⟨hy, (hValue x y).mpr ⟨hx, hy, hφxy⟩⟩, ?_⟩
    rintro z ⟨hz, hxz⟩
    exact hUnique z ⟨hz, ((hValue x z).mp hxz).2.2⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFunctionRelation
