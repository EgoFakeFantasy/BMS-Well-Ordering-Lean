import BMSConstructibleBridge.PowerlessRelativeLimitProduct
import BMSConstructibleBridge.PowerlessRelativeClassRelation
import BMSConstructibleBridge.PowerlessRelativeLimitDeltaSeparation

/-! # 指定极限层内的有界关系图

母积及有限参数均在给定层中，分离后仍留在这一层。全部坐标规格在原商
上成立，不以类内存在或事后放大层界替代固定层收纳。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitRelationalGraph

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B β C : type_l hℳ}

/-- 同一层内分离图的全部原商成员读数；不允许坐标域外垃圾成员。 -/
theorem exists_member_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    {X Y : type_l hℳ} (hX : mem_l hℳ X C) (hY : mem_l hℳ Y C)
    (hParams : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) C) :
    ∃ R, mem_l hℳ R C ∧ ∀ p : type_l hℳ,
      mem_l hℳ p R ↔ ∃ x y, mem_l hℳ x X ∧ mem_l hℳ y Y ∧
        ordered_l (ℳ := SecondOrderQuotient.structure_l hℳ) x y p ∧
          φ.satisfies ((η.pushFree y).pushFree x) := by
  obtain ⟨P, hP⟩ := SecondOrderDefinableRelationImage.exists_l hℳ (Δ := []) .truth Env.empty X Y
  have hProduct : ∀ p, mem_l hℳ p P ↔ ∃ x y, mem_l hℳ x X ∧ mem_l hℳ y Y ∧
      SecondOrderPairObjects.ordered_l hℳ x y p := by
    simpa only [Formula.satisfies, true_and] using hP
  have hPC := PowerlessRelativeLimitProduct.member_l hBase hLimit hC hX hY hProduct
  let η' : Env (SecondOrderQuotient.structure_l hℳ) [] (.set :: .set :: Δ) :=
    (η.pushFree Y).pushFree X
  have hParams' : ∀ s (v : Variable (.set :: .set :: Δ) s), mem_l hℳ (η'.freeVal v) C := by
    intro s v
    cases v with
    | here => exact hX
    | there v => cases v with
      | here => exact hY
      | there v => exact hParams _ v
  obtain ⟨R, hRC, hR⟩ := PowerlessRelativeLimitDeltaSeparation.exists_l hBase hLimit hC
    (PowerlessRelativeClassRelation.body_delta_l hφ) η' hPC hParams'
  have hRead p : mem_l hℳ p R ↔ ∃ x y, mem_l hℳ x X ∧ mem_l hℳ y Y ∧
      ordered_l (ℳ := SecondOrderQuotient.structure_l hℳ) x y p ∧
        φ.satisfies ((η.pushFree y).pushFree x) := by
    have hBody := PowerlessRelativeClassRelation.body_formula_l φ η X Y p
    constructor
    · intro hp
      exact hBody.mp ((hR p).mp hp).2
    · rintro ⟨x, y, hx, hy, hxy, hφxy⟩
      exact (hR p).mpr ⟨(hProduct p).mpr ⟨x, y, hx, hy, hxy⟩,
        hBody.mpr ⟨x, y, hx, hy, hxy, hφxy⟩⟩
  exact ⟨R, hRC, hRead⟩

/-- 已取得的同一张成员图给出全部原商坐标的取值读数，不重新选择关系图。 -/
theorem values_of_members_l
    {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    {η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ} {X Y R : type_l hℳ}
    (hRead : ∀ p : type_l hℳ,
      mem_l hℳ p R ↔ ∃ x y, mem_l hℳ x X ∧ mem_l hℳ y Y ∧
        ordered_l (ℳ := SecondOrderQuotient.structure_l hℳ) x y p ∧
          φ.satisfies ((η.pushFree y).pushFree x)) :
    ∀ x y : type_l hℳ,
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) R x y ↔
        mem_l hℳ x X ∧ mem_l hℳ y Y ∧ φ.satisfies ((η.pushFree y).pushFree x) := by
  intro x y
  constructor
  · rintro ⟨p, hp, hxy⟩
    obtain ⟨a, b, ha, hb, hab, hφab⟩ := (hRead p).mp hp
    obtain ⟨rfl, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hxy hab).mp rfl
    exact ⟨ha, hb, hφab⟩
  · rintro ⟨hx, hy, hφxy⟩
    obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ x y
    exact ⟨p, (hRead p).mpr ⟨x, y, hx, hy, hp, hφxy⟩, hp⟩

/-- 原接口由同一张完整成员图派生，保持全部原商坐标的取值规格。 -/
theorem exists_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    {X Y : type_l hℳ} (hX : mem_l hℳ X C) (hY : mem_l hℳ Y C)
    (hParams : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) C) :
    ∃ R, mem_l hℳ R C ∧ ∀ x y : type_l hℳ,
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) R x y ↔
        mem_l hℳ x X ∧ mem_l hℳ y Y ∧ φ.satisfies ((η.pushFree y).pushFree x) := by
  obtain ⟨R, hRC, hRead⟩ := exists_member_l hBase hLimit hC hφ η hX hY hParams
  exact ⟨R, hRC, values_of_members_l hRead⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitRelationalGraph
