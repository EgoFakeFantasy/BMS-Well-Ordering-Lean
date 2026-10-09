import BMSConstructibleBridge.PowerlessRelativeClassRelation
import BMSConstructibleBridge.PowerlessRelativeLimitClosure
import BMSConstructibleBridge.SecondOrderMemberDefBoundedSlice

/-! # 极限层上的有界可定义函数图进入两次 Def

在实际相对极限层 W 上给定 raw 函数图 G 及一个实际纯 Δ₀ 矩阵。
定义域和值域的成员留在 W 中，因此每个图成员的实际有序对也留在 W；
W ⊆ D = Def(W) 后，图可作为 D 上的有界可定义切片进入 E = Def(D)。

全部矩阵参数、定义域和值域只要求属于 D，不要求属于 W：矩阵可以直接
使用 W 自身作为参数。这里给通用的有限两 Def 界，不使用 Collection、
历史或迭代前提，不构造共同界，也不宣称对象推导终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitFunctionGraphBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

/-- 图的 raw 读数、实际 Δ₀ 正文和两次 Def 给出原商集合中的明确成员界。 -/
theorem member_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {B γ W D E Domain Range G : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B γ W)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ γ)
    (hWD : SecondOrderMemberDef.spec_l hℳ W D) (hDE : SecondOrderMemberDef.spec_l hℳ D E)
    {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    (hParamsD : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) D)
    (hDomainD : mem_l hℳ Domain D) (hRangeD : mem_l hℳ Range D)
    (hDomainW : ∀ x, mem_l hℳ x Domain → mem_l hℳ x W)
    (hRangeW : ∀ y, mem_l hℳ y Range → mem_l hℳ y W)
    (hG : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) G Domain Range)
    (hRead : ∀ x y, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G x y ↔
      mem_l hℳ x Domain ∧ mem_l hℳ y Range ∧ φ.satisfies ((η.pushFree y).pushFree x)) :
    mem_l hℳ G E := by
  let ξ : Env (SecondOrderQuotient.structure_l hℳ) [] (.set :: .set :: Δ) :=
    (η.pushFree Range).pushFree Domain
  have hTransW := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hW
  have hSub := SecondOrderMemberDefProperties.contains_l hℳ hWD
    (fun x y hx hy => hTransW x hx y hy)
  have hTransD := SecondOrderMemberDefProperties.transitive_l hℳ hWD
    (fun x y hx hy => hTransW x hx y hy)
  apply SecondOrderMemberDefBoundedSlice.member_l hℳ hDE
    (fun x hx y hy => hTransD x y hx hy) (PowerlessRelativeClassRelation.body_delta_l hφ) ξ
  · intro s v
    cases s
    cases v with
    | here => exact hDomainD
    | there v =>
        cases v with
        | here => exact hRangeD
        | there v => exact hParamsD _ v
  · intro p
    change mem_l hℳ p G ↔ mem_l hℳ p D ∧
      (PowerlessRelativeClassRelation.body_m φ).satisfies
        (((η.pushFree Range).pushFree Domain).pushFree p)
    rw [PowerlessRelativeClassRelation.body_formula_l φ η Domain Range p]
    constructor
    · intro hp
      obtain ⟨x, y, hx, hy, hPair⟩ := hG.1 p hp
      have hpW := PowerlessRelativeLimitClosure.ordered_l hℳ hBase hLimit hW
        (hDomainW x hx) (hRangeW y hy) hPair
      have hValue : value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G x y := ⟨p, hp, hPair⟩
      exact ⟨hSub p hpW, x, y, hx, hy, hPair, ((hRead x y).mp hValue).2.2⟩
    · rintro ⟨_, x, y, hx, hy, hPair, hxy⟩
      obtain ⟨q, hq, hPair'⟩ := (hRead x y).mpr ⟨hx, hy, hxy⟩
      exact (SecondOrderPairObjects.ordered_unique_l hℳ hPair' hPair) ▸ hq

#print axioms member_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitFunctionGraphBounded
