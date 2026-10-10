import BMSConstructibleBridge.PowerlessBMSQuotientSubsetImage
import BMSConstructibleBridge.SecondOrderDefinableRelationImage
import BMSConstructibleBridge.SecondOrderFunctionLaws
import BMSConstructibleBridge.ThirdOrderSemantics

/-! # 自然数索引、子集有界的可定义函数图

先用原 Z₂ 的子集切片构造精确值域，再构造完整函数图。
逐数存在唯一性不被当成可数选择；统一子集界是显式前提。
用于实数历史解码后的图历史恢复，不证明递归历史本身已存在。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientSubsetFunction

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private def swap_m {Δ : SortContext ℒ} :
    Substitution ℒ [] (.set :: .set :: Δ) [] (.set :: .set :: Δ) :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => .fvar (.there .here)
    | .there .here => .fvar .here
    | .there (.there v) => .fvar (.there (.there v)))

private theorem swap_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 [] Δ)
    (x y : 𝒩.Carrier .set) :
    (φ.substitute swap_m).satisfies ((η.pushFree y).pushFree x) ↔
      φ.satisfies ((η.pushFree x).pushFree y) := by
  refine (Formula.satisfies_substitute _ _ φ).trans ?_
  apply Iff.of_eq
  apply congrArg (fun ξ => φ.satisfies ξ)
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    cases v with
    | here => rfl
    | there v => cases v <;> rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 输出槽在索引槽之前，与既有子集有界替换接口保持一致。 -/
theorem exists_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ) (a : type_l hℳ)
    (hTotal : ∀ n, ∃ y, φ.satisfies ((η.pushFree (numberCode_l K n).val).pushFree y))
    (hUnique : ∀ n y z,
      φ.satisfies ((η.pushFree (numberCode_l K n).val).pushFree y) →
      φ.satisfies ((η.pushFree (numberCode_l K n).val).pushFree z) → y = z)
    (hBound : ∀ n y, φ.satisfies ((η.pushFree (numberCode_l K n).val).pushFree y) →
      ∀ x, mem_l hℳ x y → mem_l hℳ x a) :
    ∃ b g : type_l hℳ,
      (∀ y, mem_l hℳ y b ↔ ∃ n, φ.satisfies ((η.pushFree (numberCode_l K n).val).pushFree y)) ∧
      map_l (ℳ := 𝒱) g K.omega b ∧
      ∀ x y, value_l (ℳ := 𝒱) g x y ↔
        mem_l hℳ x K.omega ∧ φ.satisfies ((η.pushFree x).pushFree y) := by
  obtain ⟨b, hb⟩ := PowerlessBMSQuotientSubsetImage.exists_l K φ η a hTotal hUnique hBound
  obtain ⟨g, hg⟩ := SecondOrderDefinableRelationImage.exists_l hℳ
    (φ.substitute swap_m) η K.omega b
  have hRead (x y : type_l hℳ) : value_l (ℳ := 𝒱) g x y ↔
      mem_l hℳ x K.omega ∧ φ.satisfies ((η.pushFree x).pushFree y) := by
    constructor
    · rintro ⟨p, hp, hxy⟩
      obtain ⟨v, w, hv, _, hvw, hp'⟩ := (hg p).mp hp
      obtain ⟨rfl, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hxy hp').mp rfl
      exact ⟨hv, (swap_formula_l φ η x y).mp hvw⟩
    · rintro ⟨hx, hxy⟩
      obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨x, hx⟩
      have hn' : (numberCode_l K n).val = x := congrArg Subtype.val hn
      have hy : mem_l hℳ y b := (hb y).mpr ⟨n, hn'.symm ▸ hxy⟩
      obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ x y
      exact ⟨p, (hg p).mpr ⟨x, y, hx, hy, (swap_formula_l φ η x y).mpr hxy, hp⟩, hp⟩
  refine ⟨b, g, hb, ⟨?_, ?_⟩, hRead⟩
  · intro p hp
    obtain ⟨x, y, hx, hy, _, hxy⟩ := (hg p).mp hp
    exact ⟨x, y, hx, hy, hxy⟩
  · intro x hx
    obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨x, hx⟩
    have hn' : (numberCode_l K n).val = x := congrArg Subtype.val hn
    obtain ⟨y, hy⟩ := hTotal n
    refine ⟨y, ⟨(hb y).mpr ⟨n, hy⟩, (hRead x y).mpr ⟨hx, hn' ▸ hy⟩⟩, ?_⟩
    rintro z ⟨_, hz⟩
    have hz' := (hRead x z).mp hz
    rw [← hn'] at hz'
    exact hUnique n z y hz'.2 hy

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientSubsetFunction
