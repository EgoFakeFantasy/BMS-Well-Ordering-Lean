import BMSConstructibleBridge.PowerlessRelativeClassRelationalGraph

/-! # 类内关系图的全环境成员规格

逐值规格可能忽略非有序对垃圾。本接口保留类内 Δ₀ 分离所得图的
全部实际成员，并把坐标、编码和正文一并传到全原商，供规范图唯一性使用。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassRelationAmbientMembers

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

/-- 固定两坐标的环境传输，保留原有界公式及参数环境。 -/
theorem formula_absolute_l {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) (η : Env (structure_l hℳ B hBase) [] Δ)
    (x y : type_l hℳ B) :
    φ.satisfies ((η.pushFree y).pushFree x) ↔
      φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree y.val).pushFree x.val) := by
  have hEnv : PowerlessRelativeClassRelativization.env_l ((η.pushFree y).pushFree x) =
      ((PowerlessRelativeClassRelativization.env_l η).pushFree (sort := SetTheory.SetSort.set) y.val).pushFree
        (sort := SetTheory.SetSort.set) x.val := by
    apply Env.ext
    · intro s v; nomatch v
    · intro s v
      cases s
      cases v with
      | here => rfl
      | there v => cases v <;> rfl
  have hAbsolute := PowerlessRelativeClassBounded.formula_l hφ ((η.pushFree y).pushFree x)
  rw [hEnv] at hAbsolute
  exact hAbsolute

theorem exists_l {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) (η : Env (structure_l hℳ B hBase) [] Δ)
    (X Y : type_l hℳ B) : ∃ G : type_l hℳ B, ∀ p : SecondOrderQuotient.type_l hℳ,
      mem_l hℳ p G.val ↔ ∃ x y : SecondOrderQuotient.type_l hℳ,
        mem_l hℳ x X.val ∧ mem_l hℳ y Y.val ∧
          SecondOrderPairObjects.ordered_l hℳ x y p ∧
            φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree y).pushFree x) := by
  obtain ⟨G, hG⟩ := PowerlessRelativeClassRelation.exists_l hφ η X Y
  refine ⟨G, fun p => ⟨?_, ?_⟩⟩
  · intro hp
    let P : type_l hℳ B := ⟨p,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase G.property hp⟩
    obtain ⟨x, y, hx, hy, hxy, hBody⟩ := (hG P).mp hp
    exact ⟨x.val, y.val, hx, hy,
      (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) x y P).mp hxy,
      (formula_absolute_l hφ η x y).mp hBody⟩
  · rintro ⟨x, y, hx, hy, hxy, hBody⟩
    let X' : type_l hℳ B := ⟨x,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase X.property hx⟩
    let Y' : type_l hℳ B := ⟨y,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Y.property hy⟩
    let P : type_l hℳ B := ⟨p,
      PowerlessRelativeClassPair.ordered_l hℳ hBase X'.property Y'.property hxy⟩
    exact (hG P).mpr ⟨X', Y', hx, hy,
      (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) X' Y' P).mpr hxy,
      (formula_absolute_l hφ η X' Y').mpr hBody⟩

#print axioms exists_l

/-- 精确成员图同时提供逐值接口；两者不能互相混淆。 -/
theorem exists_spec_l {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) (η : Env (structure_l hℳ B hBase) [] Δ)
    (X Y : type_l hℳ B) : ∃ G : type_l hℳ B,
      (∀ p : SecondOrderQuotient.type_l hℳ, mem_l hℳ p G.val ↔
        ∃ x y : SecondOrderQuotient.type_l hℳ, mem_l hℳ x X.val ∧ mem_l hℳ y Y.val ∧
          SecondOrderPairObjects.ordered_l hℳ x y p ∧
            φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree y).pushFree x)) ∧
      (∀ x y : type_l hℳ B, value_l (ℳ := structure_l hℳ B hBase) G x y ↔
        mem_l hℳ x.val X.val ∧ mem_l hℳ y.val Y.val ∧ φ.satisfies ((η.pushFree y).pushFree x)) := by
  obtain ⟨G, hG⟩ := exists_l hφ η X Y
  have hRaw (x y : type_l hℳ B) :
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G.val x.val y.val ↔
        mem_l hℳ x.val X.val ∧ mem_l hℳ y.val Y.val ∧
          φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree y.val).pushFree x.val) := by
    constructor
    · rintro ⟨p, hp, hxy⟩
      obtain ⟨a, b, ha, hb, hab, hBody⟩ := (hG p).mp hp
      obtain ⟨rfl, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hab hxy).mp rfl
      exact ⟨ha, hb, hBody⟩
    · rintro ⟨hx, hy, hBody⟩
      obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ x.val y.val
      exact ⟨p, (hG p).mpr ⟨x.val, y.val, hx, hy, hp, hBody⟩, hp⟩
  refine ⟨G, hG, fun x y => ?_⟩
  exact (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) G x y).trans
    ((hRaw x y).trans (and_congr Iff.rfl (and_congr Iff.rfl (formula_absolute_l hφ η x y).symm)))

#print axioms exists_spec_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassRelationAmbientMembers
