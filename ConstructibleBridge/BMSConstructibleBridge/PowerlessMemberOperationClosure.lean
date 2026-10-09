import BMSConstructibleBridge.PowerlessSourceGraphAbsolute
import BMSConstructibleBridge.PowerlessRelativeFiniteHullAssignments

/-! # 传递外层中的同一子域操作闭包

对象语言为纯隶属 ℒ。外层 W 的实际传递性及配对／二元并闭包，保证
任意真实候选操作结果都在 W 中，因此成员域对子域 U 的完整闭包
断言与原环境断言精确对应。不要求 U 传递、U 是层或 W 满足源理论。
这里只是语义绝对性接口，不替代最终对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberOperationClosure

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l
  PowerlessMemberStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {W : carrier_l ℳ}
  {hW : ∃ x, member_l ℳ x W}

local notation "𝒩₀" => PowerlessMemberStructure.structure_l (ℳ := ℳ) W hW
local notation "M" => PowerlessMemberStructure.type_l (ℳ := ℳ) W

theorem transitive_l (hTrans : PowerlessNaturalOrder.transitive_l (ℳ := ℳ) W) (U : M) :
    PowerlessNaturalOrder.transitive_l (ℳ := 𝒩₀) U ↔
      PowerlessNaturalOrder.transitive_l (ℳ := ℳ) U.val := by
  constructor
  · intro h a b ha hb
    let a₀ : M := ⟨a, hTrans U.val a U.property ha⟩
    let b₀ : M := ⟨b, hTrans a b a₀.property hb⟩
    exact h a₀ b₀ ha hb
  · intro h a b ha hb
    exact h a.val b.val ha hb

/-- 全部 raw 操作结果由 W 的实际闭包取得，不缩小子域闭包的候选范围。 -/
theorem closed_l (hTrans : PowerlessNaturalOrder.transitive_l (ℳ := ℳ) W)
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := ℳ) W) (U : M) :
    PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒩₀) U ↔
      PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := ℳ) U.val := by
  constructor
  · intro h
    constructor
    · intro a b p ha hb hp
      let a₀ : M := ⟨a, hTrans U.val a U.property ha⟩
      let b₀ : M := ⟨b, hTrans U.val b U.property hb⟩
      let p₀ : M := ⟨p, hClosed.1 a b p a₀.property b₀.property hp⟩
      exact h.1 a₀ b₀ p₀ ha hb ((PowerlessSourceGraphAbsolute.pair_l hTrans).mpr hp)
    · intro a b c ha hb hc
      let a₀ : M := ⟨a, hTrans U.val a U.property ha⟩
      let b₀ : M := ⟨b, hTrans U.val b U.property hb⟩
      let c₀ : M := ⟨c, hClosed.2 a b c a₀.property b₀.property hc⟩
      exact h.2 a₀ b₀ c₀ ha hb (fun z => hc z.val)
  · intro h
    constructor
    · intro a b p ha hb hp
      exact h.1 a.val b.val p.val ha hb ((PowerlessSourceGraphAbsolute.pair_l hTrans).mp hp)
    · intro a b c ha hb hc
      apply h.2 a.val b.val c.val ha hb
      intro z
      constructor
      · intro hz
        exact (hc ⟨z, hTrans c.val z c.property hz⟩).mp hz
      · rintro (hz | hz)
        · exact (hc ⟨z, hTrans a.val z a.property hz⟩).mpr (Or.inl hz)
        · exact (hc ⟨z, hTrans b.val z b.property hz⟩).mpr (Or.inr hz)

#print axioms transitive_l
#print axioms closed_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberOperationClosure
