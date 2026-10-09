import BMSConstructibleBridge.PowerlessRelativeClassFunctionRelation
import BMSConstructibleBridge.SecondOrderFunctionProperties

/-! # 实际 Class 函数图的全原商读数

既有 Δ₀ 函数图构造只需类内总单值性。此接口同时保留干净映射，
用有界绝对性与实际坐标界取得类外元素也受约束的原商规格。
不改变旧函数关系模块的接口，不从 Type 抽取图或选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFunctionGraph

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
    ∃ f : type_l hℳ B,
      map_l (ℳ := SecondOrderQuotient.structure_l hℳ) f.val X.val Y.val ∧
        ∀ x y : SecondOrderQuotient.type_l hℳ,
          value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f.val x y ↔
            mem_l hℳ x X.val ∧ mem_l hℳ y Y.val ∧ φ.satisfies
              (((PowerlessRelativeClassRelativization.env_l η).pushFree y).pushFree x) := by
  obtain ⟨f, hf, hRead⟩ := PowerlessRelativeClassFunctionRelation.exists_l hφ η X Y hTotal
  have hMap := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f X Y).mp hf
  have hValue (x y : type_l hℳ B) :
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f.val x.val y.val ↔
      mem_l hℳ x.val X.val ∧ mem_l hℳ y.val Y.val ∧ φ.satisfies
        (((PowerlessRelativeClassRelativization.env_l η).pushFree y.val).pushFree x.val) := by
    have hEnv : PowerlessRelativeClassRelativization.env_l ((η.pushFree y).pushFree x) =
        ((PowerlessRelativeClassRelativization.env_l η).pushFree
          (sort := SetTheory.SetSort.set) y.val).pushFree (sort := SetTheory.SetSort.set) x.val := by
      apply Env.ext
      · intro s v; nomatch v
      · intro s v
        cases s
        cases v with
        | here => rfl
        | there v => cases v <;> rfl
    have hAbsolute := PowerlessRelativeClassBounded.formula_l hφ ((η.pushFree y).pushFree x)
    rw [hEnv] at hAbsolute
    exact (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f x y).symm.trans
      ((hRead x y).trans (and_congr Iff.rfl (and_congr Iff.rfl hAbsolute)))
  refine ⟨f, hMap, fun x y => ⟨?_, ?_⟩⟩
  · intro hxy
    obtain ⟨hx, hy⟩ := SecondOrderFunctionProperties.value_mem_l hℳ hMap hxy
    exact (hValue
      ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase X.property hx⟩
      ⟨y, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Y.property hy⟩).mp hxy
  · rintro ⟨hx, hy, hxy⟩
    exact (hValue
      ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase X.property hx⟩
      ⟨y, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Y.property hy⟩).mpr ⟨hx, hy, hxy⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFunctionGraph
