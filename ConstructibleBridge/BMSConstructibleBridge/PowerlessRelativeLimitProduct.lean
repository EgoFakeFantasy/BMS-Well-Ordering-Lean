import BMSConstructibleBridge.PowerlessRelativeClassProduct
import BMSConstructibleBridge.PowerlessRelativeLimitClosure

/-! # 给定非零极限层中的实际笛卡尔积

将两个参数置于严格较早的共同层，连续三个 Def 后继仍严格低于给定
极限阶段。全部原商有序对的实际积因而属于这个预定层，而非仅属于并类。
这里只提供固定层的语义闭包接口，供有界关系图构造使用。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitProduct

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)
open PowerlessRelativeClassProduct (body_m body_delta_l body_formula_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B β C : type_l hℳ}

/-- 全部原商坐标上的积规格保证积属于同一个给定的非零极限层。 -/
theorem member_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    {X Y P : type_l hℳ} (hX : mem_l hℳ X C) (hY : mem_l hℳ Y C)
    (hP : ∀ p, mem_l hℳ p P ↔ ∃ x y, mem_l hℳ x X ∧ mem_l hℳ y Y ∧
      SecondOrderPairObjects.ordered_l hℳ x y p) : mem_l hℳ P C := by
  obtain ⟨a, c, ha, hc, hXc, hYc⟩ :=
    PowerlessRelativeLimitClosure.common_l hℳ hBase hLimit hC hX hY
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hc
  obtain ⟨a₁, c₁, ha₁, hc₁, hDef₁⟩ :=
    PowerlessRelativeLimitClosure.def_bound_l hℳ hBase hLimit hC ha hc
  obtain ⟨a₂, c₂, ha₂, hc₂, hDef₂⟩ :=
    PowerlessRelativeLimitClosure.def_bound_l hℳ hBase hLimit hC ha₁ hc₁
  obtain ⟨a₃, c₃, ha₃, hc₃, hDef₃⟩ :=
    PowerlessRelativeLimitClosure.def_bound_l hℳ hBase hLimit hC ha₂ hc₂
  have hTrans₁ := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hc₁
  have hTrans₂ := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hc₂
  have hKeep₁ := SecondOrderMemberDefProperties.contains_l hℳ hDef₁
    (fun x y hx hy => hTrans x hx y hy)
  have hKeep₂ := SecondOrderMemberDefProperties.contains_l hℳ hDef₂
    (fun x y hx hy => hTrans₁ x hx y hy)
  have hPairs {x y p : type_l hℳ} (hx : mem_l hℳ x X) (hy : mem_l hℳ y Y)
      (hp : SecondOrderPairObjects.ordered_l hℳ x y p) : mem_l hℳ p c₂ := by
    obtain ⟨s, t, hs, ht, hp⟩ := hp
    have hxC := hTrans X hXc x hx
    have hyC := hTrans Y hYc y hy
    exact SecondOrderMemberDefPair.member_l hℳ hDef₂
      (SecondOrderMemberDefPair.member_l hℳ hDef₁ hxC hxC hs)
      (SecondOrderMemberDefPair.member_l hℳ hDef₁ hxC hyC ht) hp
  let η := (Env.empty (M := SecondOrderQuotient.structure_l hℳ)).pushFree
    (sort := SetTheory.SetSort.set) Y |>.pushFree (sort := SetTheory.SetSort.set) X
  let φ : Formula ℒ [] [.set, .set, .set] := body_m (.fvar (.there .here))
    (.fvar (.there (.there .here))) (.fvar .here)
  have hParams : ∀ (s : SetTheory.SetSort)
      (v : Variable [SetTheory.SetSort.set, SetTheory.SetSort.set] s),
      mem_l hℳ (η.freeVal v) c₂ := by
    intro s v
    cases s
    cases v with
    | here => exact hKeep₂ X (hKeep₁ X hXc)
    | there v => cases v with
      | here => exact hKeep₂ Y (hKeep₁ Y hYc)
      | there v => nomatch v
  have hSlice : ∀ p, mem_l hℳ p P ↔ mem_l hℳ p c₂ ∧ φ.satisfies (η.pushFree p) := by
    intro p
    have hBody := body_formula_l (η.pushFree (sort := SetTheory.SetSort.set) p)
      (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
    constructor
    · intro hp
      obtain ⟨x, y, hx, hy, hxy⟩ := (hP p).mp hp
      exact ⟨hPairs hx hy hxy, hBody.mpr ⟨x, y, hx, hy, hxy⟩⟩
    · rintro ⟨_, hp⟩
      exact (hP p).mpr (hBody.mp hp)
  exact (PowerlessRelativeLimitClosure.value_l hℳ hBase hLimit hC P).mpr
    ⟨a₃, c₃, ha₃, hc₃, SecondOrderMemberDefBoundedSlice.member_l hℳ hDef₃ hTrans₂
      (body_delta_l _ _ _) η hParams hSlice⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitProduct
