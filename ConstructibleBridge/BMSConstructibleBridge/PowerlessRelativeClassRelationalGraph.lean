import BMSConstructibleBridge.PowerlessRelativeClassFunctionRelation
import BMSConstructibleBridge.PowerlessRelativeClassValueCoordinates

/-! # 有界类关系的逐值图接口

关系无需全域或单值；图值精确等于有界坐标上的原公式。规范编号先需要
多编号关系，不能为了调用函数接口提前假设每个输入都有唯一输出。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassRelationalGraph

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
    (X Y : type_l hℳ B) : ∃ G : type_l hℳ B,
      ∀ x y : type_l hℳ B, value_l (ℳ := structure_l hℳ B hBase) G x y ↔
        mem_l hℳ x.val X.val ∧ mem_l hℳ y.val Y.val ∧ φ.satisfies ((η.pushFree y).pushFree x) := by
  obtain ⟨G, hG⟩ := PowerlessRelativeClassRelation.exists_l hφ η X Y
  refine ⟨G, fun x y => ⟨?_, ?_⟩⟩
  · rintro ⟨p, hp, hxy⟩
    obtain ⟨a, b, ha, hb, hab, hφab⟩ := (hG p).mp hp
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
    exact ⟨p', (hG p').mpr ⟨x, y, hx, hy, hp', hφxy⟩, hp'⟩

/-- 全原商坐标规格；类外坐标由传递性排除，公式通过有界绝对性读取。 -/
theorem exists_ambient_l {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) (η : Env (structure_l hℳ B hBase) [] Δ)
    (X Y : type_l hℳ B) : ∃ G : type_l hℳ B,
      ∀ x y : SecondOrderQuotient.type_l hℳ,
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G.val x y ↔
          mem_l hℳ x X.val ∧ mem_l hℳ y Y.val ∧
            φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree y).pushFree x) := by
  obtain ⟨G, hG⟩ := exists_l hφ η X Y
  have hRead (x y : type_l hℳ B) :
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G.val x.val y.val ↔
        mem_l hℳ x.val X.val ∧ mem_l hℳ y.val Y.val ∧
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
    exact (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) G x y).symm.trans
      ((hG x y).trans (and_congr Iff.rfl (and_congr Iff.rfl hAbsolute)))
  refine ⟨G, fun x y => ⟨?_, ?_⟩⟩
  · intro hValue
    obtain ⟨hx, hy⟩ := PowerlessRelativeClassValueCoordinates.value_l hBase G hValue
    exact (hRead ⟨x, hx⟩ ⟨y, hy⟩).mp hValue
  · rintro ⟨hx, hy, hBody⟩
    exact (hRead
      ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase X.property hx⟩
      ⟨y, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Y.property hy⟩).mpr ⟨hx, hy, hBody⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassRelationalGraph
