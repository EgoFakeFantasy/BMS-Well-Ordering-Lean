import BMSConstructibleBridge.PowerlessRelativeClassFunctionExtension
import BMSConstructibleBridge.PowerlessRelativeClassBinaryUnion

/-! # 内部有限前史的可变值域单步扩展

新输出不必预先属于旧值域。仅将一个输出加入值域，再扩展一个图节点；
两项见证仍在同一相对并类中。此接口不预设整条无限历史的共同值域界，
不使用 Collection，也不声称已经构造无限历史。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFunctionRangeExtension

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒞" => structure_l hℳ B hBase

theorem codomain_l {f A D W : type_l hℳ B} (hf : map_l (ℳ := 𝒞) f A D)
    (hDW : subset_l (ℳ := 𝒞) D W) : map_l (ℳ := 𝒞) f A W := by
  have hRaw := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f A D).mp hf
  constructor
  · intro p hp
    obtain ⟨x, y, hx, hy, hxy⟩ := hf.1 p hp
    exact ⟨x, y, hx, hDW y hy, hxy⟩
  · intro x hx
    obtain ⟨y, hy, _⟩ := hf.2 x hx
    refine ⟨y, ⟨hDW y hy.1, hy.2⟩, ?_⟩
    intro z hz
    exact Subtype.ext (SecondOrderFunctionProperties.value_unique_l hℳ hRaw
      ((PowerlessRelativeClassFunctionAbsolute.value_l f x z).mp hz.2)
      ((PowerlessRelativeClassFunctionAbsolute.value_l f x y).mp hy.2))

theorem exists_l {f A D S c d : type_l hℳ B} (hf : map_l (ℳ := 𝒞) f A D)
    (hc : ¬mem_l hℳ c.val A.val)
    (hS : ∀ x : type_l hℳ B, mem_l hℳ x.val S.val ↔ mem_l hℳ x.val A.val ∨ x = c) :
    ∃ W g : type_l hℳ B,
      (∀ y : type_l hℳ B, mem_l hℳ y.val W.val ↔ mem_l hℳ y.val D.val ∨ y = d) ∧
      map_l (ℳ := 𝒞) g S W ∧
      ∀ x y : type_l hℳ B, value_l (ℳ := 𝒞) g x y ↔ value_l (ℳ := 𝒞) f x y ∨ x = c ∧ y = d := by
  obtain ⟨p, hp⟩ := SecondOrderPairObjects.pair_exists_l hℳ d.val d.val
  let p' : type_l hℳ B := ⟨p, PowerlessRelativeClassPair.pair_l hℳ hBase d.property d.property hp⟩
  obtain ⟨W, hW⟩ := PowerlessRelativeClassBinaryUnion.exists_l (hBase := hBase) D p'
  have hMembers (y : type_l hℳ B) : mem_l hℳ y.val W.val ↔ mem_l hℳ y.val D.val ∨ y = d := by
    refine (hW y).trans (or_congr Iff.rfl ?_)
    exact (hp y.val).trans ⟨fun h => Subtype.ext (h.elim id id), fun h => Or.inl (congrArg Subtype.val h)⟩
  have hNew : map_l (ℳ := 𝒞) f A W := codomain_l hf (fun y hy => (hMembers y).mpr (Or.inl hy))
  obtain ⟨g, hg, hRead⟩ := PowerlessRelativeClassFunctionExtension.exists_l
    (hBase := hBase) (f := f) (A := A) (D := W) (S := S) (c := c) (d := d)
    hNew hc ((hMembers d).mpr (Or.inr rfl)) hS
  exact ⟨W, g, hMembers, hg, hRead⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFunctionRangeExtension
