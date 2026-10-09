import BMSConstructibleBridge.PowerlessBMSPartialTransitiveImage
import BMSConstructibleBridge.SecondOrderCountabilityAxiom

/-!
# 任意内部集合定义域的传递类像

用实际内部单射将定义域送入 ω，再将原关系拉回成自然数索引的部分函数。
所有变量、参数、函数图都在同一原图商中；不以外部可数枚举代替内部单射。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSSetTransitiveImage

open Logic FirstOrder PowerlessBMSQuotientCoding

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private def insert_m {Δ : SortContext ℒ} :
    VariableSubstitution ℒ (.set :: .set :: Δ) [.set] (.set :: .set :: .set :: .set :: Δ)
  | _, .here => .fvar .here
  | _, .there .here => .bvar .here
  | _, .there (.there v) => .fvar (.there (.there (.there (.there v))))

/-- 自由槽为输出、数输入、单射图、原定义域及原参数。 -/
def pullback_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (.set :: .set :: .set :: .set :: Δ) :=
  .existsE .set (.conj
    (SecondOrderObjectSyntax.member_m (.bvar .here) (.fvar (.there (.there (.there .here)))))
    (.conj (SecondOrderObjectSyntax.value_m (.fvar (.there (.there .here)))
      (.bvar .here) (.fvar (.there .here)))
      (φ.substitute (show Substitution ℒ [] (.set :: .set :: Δ) [.set]
        (.set :: .set :: .set :: .set :: Δ) from .map (fun v => nomatch v) insert_m))))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)

private abbrev quotient_l := SecondOrderQuotient.structure_l hℳ

theorem pullback_formula_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (quotient_l hℳ) [] Δ) (d f n y : SecondOrderQuotient.type_l hℳ) :
    (pullback_m φ).satisfies ((((η.pushFree d).pushFree f).pushFree n).pushFree y) ↔
      ∃ x, SecondOrderQuotient.mem_l hℳ x d ∧ SecondOrderFunctionObjects.value_l hℳ f x n ∧
        φ.satisfies ((η.pushFree x).pushFree y) := by
  simp only [pullback_m, Formula.satisfies, SecondOrderObjectSyntax.member_m,
    SecondOrderObjectSyntax.value_l, Arguments.eval, Term.eval]
  apply exists_congr
  intro x
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  refine (Formula.satisfies_substitute _ _ φ).trans ?_
  apply Iff.of_eq
  apply congrArg (fun η => φ.satisfies η)
  apply Env.ext
  · intro s v
    nomatch v
  · intro s v
    cases v with
    | here => rfl
    | there v => cases v <;> rfl

/-- 任意内部集合上的部分单值可定义关系，只要像传递，就有精确集合值域。 -/
theorem exists_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (quotient_l hℳ) [] Δ) (d : SecondOrderQuotient.type_l hℳ)
    (hUnique : ∀ x y z, SecondOrderQuotient.mem_l hℳ x d →
      φ.satisfies ((η.pushFree x).pushFree y) → φ.satisfies ((η.pushFree x).pushFree z) → y = z)
    (hTrans : ∀ x y, SecondOrderQuotient.mem_l hℳ x d → φ.satisfies ((η.pushFree x).pushFree y) →
      ∀ z, SecondOrderQuotient.mem_l hℳ z y →
        ∃ w, SecondOrderQuotient.mem_l hℳ w d ∧ φ.satisfies ((η.pushFree w).pushFree z)) :
    ∃ b, ∀ y, SecondOrderQuotient.mem_l hℳ y b ↔
      ∃ x, SecondOrderQuotient.mem_l hℳ x d ∧ φ.satisfies ((η.pushFree x).pushFree y) := by
  have hCount := SecondOrderCountabilityAxiom.models_l hℳ
  change ∀ a : SecondOrderQuotient.type_l hℳ, ∃ ω f, SecondOrderOmega.omega_l hℳ ω ∧
    SecondOrderFunctionObjects.map_l hℳ f a ω ∧ SecondOrderFunctionObjects.injective_l hℳ f at hCount
  obtain ⟨ω, f, hω, hMap, hInjective⟩ := hCount d
  obtain ⟨C⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  obtain rfl := SecondOrderOmega.unique_l hℳ hω C.omega_spec
  let ψ := pullback_m φ
  let ξ : Env (quotient_l hℳ) [] (.set :: .set :: Δ) := (η.pushFree d).pushFree f
  have hRead n y := pullback_formula_l hℳ φ η d f (numberCode_l C n).val y
  have hEnumerate x (hx : SecondOrderQuotient.mem_l hℳ x d) :
      ∃ n, SecondOrderFunctionObjects.value_l hℳ f x (numberCode_l C n).val := by
    obtain ⟨m, ⟨hm, hfm⟩, _⟩ := hMap.2 x hx
    obtain ⟨n, hn⟩ := numberCode_surjective_l C ⟨m, hm⟩
    have hn' : (numberCode_l C n).val = m := congrArg Subtype.val hn
    exact ⟨n, hn'.symm ▸ hfm⟩
  have hUnique' n y z
      (hy : ψ.satisfies ((ξ.pushFree (numberCode_l C n).val).pushFree y))
      (hz : ψ.satisfies ((ξ.pushFree (numberCode_l C n).val).pushFree z)) : y = z := by
    obtain ⟨x, hx, hfx, hy⟩ := (hRead n y).mp hy
    obtain ⟨w, _, hfw, hz⟩ := (hRead n z).mp hz
    have hxw := hInjective x w _ hfx hfw
    subst w
    exact hUnique x y z hx hy hz
  have hTrans' n y (hy : ψ.satisfies ((ξ.pushFree (numberCode_l C n).val).pushFree y))
      z (hz : SecondOrderQuotient.mem_l hℳ z y) :
      ∃ m, ψ.satisfies ((ξ.pushFree (numberCode_l C m).val).pushFree z) := by
    obtain ⟨x, hx, _, hy⟩ := (hRead n y).mp hy
    obtain ⟨w, hw, hwz⟩ := hTrans x y hx hy z hz
    obtain ⟨m, hm⟩ := hEnumerate w hw
    exact ⟨m, (hRead m z).mpr ⟨w, hw, hm, hwz⟩⟩
  obtain ⟨b, hb⟩ := PowerlessBMSPartialTransitiveImage.exists_l C ψ ξ hUnique' hTrans'
  refine ⟨b, fun y => (hb y).trans ?_⟩
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨x, hx, _, hxy⟩ := (hRead n y).mp hn
    exact ⟨x, hx, hxy⟩
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨n, hn⟩ := hEnumerate x hx
    exact ⟨n, (hRead n y).mpr ⟨x, hx, hn, hxy⟩⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSSetTransitiveImage
