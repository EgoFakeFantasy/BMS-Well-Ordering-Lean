import BMSConstructibleBridge.SecondOrderDefinableRelationImage
import BMSConstructibleBridge.SecondOrderFunctionProperties
import BMSConstructibleBridge.PowerlessBMSQuotientRecursion

/-! # 原商函数图的定义域限制

由原二阶理解构造限制图；不要求旧图预先属于相对可构造类。
此接口用于内部有限图的归纳界，不能以类内限制代替这里的任意原商参数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFunctionRestriction

open Logic FirstOrder SecondOrderQuotient SecondOrderFunctionObjects

set_option autoImplicit false
attribute [local implicit_reducible] SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem exists_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {f A D S : type_l hℳ}
    (hf : map_l hℳ f A D) (hS : ∀ x, mem_l hℳ x S → mem_l hℳ x A) :
    ∃ g, map_l hℳ g S D ∧ ∀ x y, value_l hℳ g x y ↔ mem_l hℳ x S ∧ value_l hℳ f x y := by
  let φ : Formula ℒ [] [.set, .set, .set] :=
    SecondOrderObjectSyntax.value_m (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here))
  let η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set] := (Env.empty).pushFree f
  have hφ (x y : type_l hℳ) : φ.satisfies ((η.pushFree y).pushFree x) ↔ value_l hℳ f x y := by
    exact ThirdOrderSemantics.value_formula_l _ _ _ _
  obtain ⟨g, hg⟩ := SecondOrderDefinableRelationImage.exists_l hℳ φ η S D
  have hValue (x y : type_l hℳ) : value_l hℳ g x y ↔ mem_l hℳ x S ∧ value_l hℳ f x y := by
    constructor
    · rintro ⟨p, hp, hPair⟩
      obtain ⟨x', y', hx', _, hxy', hPair'⟩ := (hg p).mp hp
      obtain ⟨rfl, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hPair hPair').mp rfl
      exact ⟨hx', (hφ x y).mp hxy'⟩
    · rintro ⟨hx, hxy⟩
      obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ x y
      exact ⟨p, (hg p).mpr ⟨x, y, hx, (SecondOrderFunctionProperties.value_mem_l hℳ hf hxy).2,
        (hφ x y).mpr hxy, hp⟩, hp⟩
  refine ⟨g, ⟨?_, ?_⟩, hValue⟩
  · intro p hp
    obtain ⟨x, y, hx, hy, _, hPair⟩ := (hg p).mp hp
    exact ⟨x, y, hx, hy, hPair⟩
  · intro x hx
    obtain ⟨y, hy, hUnique⟩ := hf.2 x (hS x hx)
    refine ⟨y, ⟨hy.1, (hValue x y).mpr ⟨hx, hy.2⟩⟩, ?_⟩
    intro z hz
    exact hUnique z ⟨hz.1, ((hValue x z).mp hz.2).2⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFunctionRestriction
