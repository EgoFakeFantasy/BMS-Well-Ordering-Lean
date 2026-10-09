import BMSConstructibleBridge.PowerlessRelativeFiniteHullClosure
import BMSConstructibleBridge.PowerlessMemberStructure

/-! # 非传递有限壳中的真实配对与图值

同一 I/W 的完整配对矩阵反射，将 MemberI 的局部配对读回原环境。
真实配对闭包回收 Kuratowski 对的全部三个见证；由此取得原图值和
MemberI 图值的双向对应。不假设 I 传递、图是函数或 I 满足源理论。
本模块是原 Z₂ 对象推导路线的语义中间工具，不是最终源模型存在证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteHullMemberValues

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature
  PowerlessMemberStructure.structure_l PowerlessMemberStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {I W : carrier_l ℳ}
  {hI : ∃ x, member_l ℳ x I}

local notation "𝒩" => PowerlessMemberStructure.structure_l I hI

/-- 完整矩阵反射而非 I 的传递性，保证局部配对没有漏掉原环境成员。 -/
theorem pair_l (hW : PowerlessNaturalOrder.transitive_l (ℳ := ℳ) W)
    (hIW : subset_l I W)
    (h : PowerlessRelativeFiniteHullClosure.pair_matrix_reflection_l I W)
    (a b p : PowerlessMemberStructure.type_l I) :
    ThirdOrderSemantics.pair_l (ℳ := ℳ) a.val b.val p.val ↔
      ThirdOrderSemantics.pair_l (ℳ := 𝒩) a b p := by
  constructor
  · intro hp z
    exact (hp z.val).trans (or_congr
      ⟨Subtype.ext, congrArg Subtype.val⟩ ⟨Subtype.ext, congrArg Subtype.val⟩)
  · intro hp
    have hLocal : PowerlessRelativeFiniteHullClosure.pair_at_l I a.val b.val p.val := by
      intro z hz
      exact (hp ⟨z, hz⟩).trans (or_congr
        ⟨congrArg Subtype.val, fun hz' => Subtype.ext hz'⟩
        ⟨congrArg Subtype.val, fun hz' => Subtype.ext hz'⟩)
    exact PowerlessRelativeFiniteHullClosure.pair_l hW
      (hIW _ a.property) (hIW _ b.property) (hIW _ p.property)
        ((h _ a.property _ b.property _ p.property).mpr hLocal)

/-- 三个无序对见证全部在同一 I 中，不从内部有序对猜测真实规格。 -/
theorem ordered_l (hW : PowerlessNaturalOrder.transitive_l (ℳ := ℳ) W)
    (hIW : subset_l I W)
    (h : PowerlessRelativeFiniteHullClosure.pair_matrix_reflection_l I W)
    (hPair : ∀ a b p, member_l ℳ a I → member_l ℳ b I →
      ThirdOrderSemantics.pair_l a b p → member_l ℳ p I)
    (a b p : PowerlessMemberStructure.type_l I) :
    ThirdOrderSemantics.ordered_l (ℳ := ℳ) a.val b.val p.val ↔
      ThirdOrderSemantics.ordered_l (ℳ := 𝒩) a b p := by
  constructor
  · rintro ⟨s, t, hs, ht, hp⟩
    let s₀ : PowerlessMemberStructure.type_l I :=
      ⟨s, hPair _ _ _ a.property a.property hs⟩
    let t₀ : PowerlessMemberStructure.type_l I :=
      ⟨t, hPair _ _ _ a.property b.property ht⟩
    exact ⟨s₀, t₀, (pair_l hW hIW h a a s₀).mp hs,
      (pair_l hW hIW h a b t₀).mp ht, (pair_l hW hIW h s₀ t₀ p).mp hp⟩
  · rintro ⟨s, t, hs, ht, hp⟩
    exact ⟨s.val, t.val, (pair_l hW hIW h a a s).mpr hs,
      (pair_l hW hIW h a b t).mpr ht, (pair_l hW hIW h s t p).mpr hp⟩

/-- 只比较给定端点的关系取值；不要求整图固定、函数性或干净成员规格。 -/
theorem value_l (hW : PowerlessNaturalOrder.transitive_l (ℳ := ℳ) W)
    (hIW : subset_l I W)
    (h : PowerlessRelativeFiniteHullClosure.pair_matrix_reflection_l I W)
    (hPair : ∀ a b p, member_l ℳ a I → member_l ℳ b I →
      ThirdOrderSemantics.pair_l a b p → member_l ℳ p I)
    (f a b : PowerlessMemberStructure.type_l I) :
    ThirdOrderSemantics.value_l (ℳ := ℳ) f.val a.val b.val ↔
      ThirdOrderSemantics.value_l (ℳ := 𝒩) f a b := by
  constructor
  · rintro ⟨p, hp, hOrdered⟩
    have hpI : member_l ℳ p I := by
      obtain ⟨s, t, hs, ht, hst⟩ := hOrdered
      exact hPair _ _ _ (hPair _ _ _ a.property a.property hs)
        (hPair _ _ _ a.property b.property ht) hst
    exact ⟨⟨p, hpI⟩, hp, (ordered_l hW hIW h hPair a b ⟨p, hpI⟩).mp hOrdered⟩
  · rintro ⟨p, hp, hOrdered⟩
    exact ⟨p.val, hp, (ordered_l hW hIW h hPair a b p).mpr hOrdered⟩

#print axioms pair_l
#print axioms ordered_l
#print axioms value_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteHullMemberValues
