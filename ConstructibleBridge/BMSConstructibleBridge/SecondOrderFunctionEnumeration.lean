import BMSConstructibleBridge.SecondOrderDefinableRelationImage
import BMSConstructibleBridge.SecondOrderFunctionLaws
import BMSConstructibleBridge.PowerlessFiniteClosureSyntax

/-!
# 集合函数的定义域与函数图之间的实际双射

把输入 x 送到函数图中的有序对 ⟨x,f(x)⟩。所有函数均为商内集合，双射图由
原公式关系像构造。有限定义域函数的整个函数图因而内部有限，无需收集。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFunctionEnumeration

open Logic FirstOrder SecondOrderFunctionObjects SecondOrderQuotient

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)

def entry_l (f x p : type_l hℳ) : Prop :=
  ∃ y, value_l hℳ f x y ∧ SecondOrderPairObjects.ordered_l hℳ x y p

def formula_m : Formula ℒ [] [.set, .set, .set] :=
  .existsE .set (.conj
    (SecondOrderObjectSyntax.value_m (.fvar (.there (.there .here))) (.fvar .here) (.bvar .here))
    (SecondOrderObjectSyntax.ordered_m (.fvar .here) (.bvar .here) (.fvar (.there .here))))

theorem formula_l (f x p : type_l hℳ) : formula_m.satisfies
    ((((Env.empty (M := SecondOrderQuotient.structure_l hℳ)).pushFree f).pushFree p).pushFree x) ↔
      entry_l hℳ f x p := by
  simp only [formula_m, Formula.satisfies, ThirdOrderSemantics.value_formula_l,
    ThirdOrderSemantics.ordered_formula_l, Term.eval]
  rfl

theorem exists_l {f a b : type_l hℳ} (hf : map_l hℳ f a b) :
    ∃ g, map_l hℳ g a f ∧
      (∀ p, mem_l hℳ p f → ∃ x, mem_l hℳ x a ∧ value_l hℳ g x p) ∧
      injective_l hℳ g := by
  obtain ⟨g, hg⟩ := SecondOrderDefinableRelationImage.exists_l hℳ formula_m
    ((Env.empty (M := SecondOrderQuotient.structure_l hℳ)).pushFree f) a f
  have hRead q : mem_l hℳ q g ↔ ∃ x p,
      mem_l hℳ x a ∧ mem_l hℳ p f ∧ entry_l hℳ f x p ∧
        SecondOrderPairObjects.ordered_l hℳ x p q := by
    rw [hg q]
    simp_rw [formula_l]
  have hValue x p : value_l hℳ g x p ↔
      mem_l hℳ x a ∧ mem_l hℳ p f ∧ entry_l hℳ f x p := by
    constructor
    · rintro ⟨q, hq, hxp⟩
      obtain ⟨z, r, hz, hr, hEntry, hzr⟩ := (hRead q).mp hq
      obtain ⟨rfl, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hxp hzr).mp rfl
      exact ⟨hz, hr, hEntry⟩
    · rintro ⟨hx, hp, hEntry⟩
      obtain ⟨q, hq⟩ := SecondOrderPairObjects.ordered_exists_l hℳ x p
      exact ⟨q, (hRead q).mpr ⟨x, p, hx, hp, hEntry, hq⟩, hq⟩
  refine ⟨g, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro q hq
    obtain ⟨x, p, hx, hp, _, hxp⟩ := (hRead q).mp hq
    exact ⟨x, p, hx, hp, hxp⟩
  · intro x hx
    obtain ⟨y, hy, _⟩ := hf.2 x hx
    obtain ⟨p, hp, hxy⟩ := hy.2
    have hxy' : value_l hℳ f x y := ⟨p, hp, hxy⟩
    refine ⟨p, ⟨hp, (hValue x p).mpr ⟨hx, hp, y, hxy', hxy⟩⟩, ?_⟩
    intro q hq
    obtain ⟨_, _, z, hxz, hxz'⟩ := (hValue x q).mp hq.2
    have hz : z = y := SecondOrderFunctionLaws.value_unique_l hℳ hf hxz hxy'
    subst z
    exact SecondOrderPairObjects.ordered_unique_l hℳ hxz' hxy
  · intro p hp
    obtain ⟨x, y, hx, _, hxy⟩ := hf.1 p hp
    exact ⟨x, hx, (hValue x p).mpr ⟨hx, hp, y, ⟨p, hp, hxy⟩, hxy⟩⟩
  · intro x z p hx hz
    obtain ⟨_, _, y, _, hxy⟩ := (hValue x p).mp hx
    obtain ⟨_, _, w, _, hzw⟩ := (hValue z p).mp hz
    exact ((SecondOrderPairObjects.ordered_eq_l hℳ hxy hzw).mp rfl).1

theorem finite_l {ω k f x : type_l hℳ} (hk : mem_l hℳ k ω)
    (hf : map_l hℳ f k x) :
    PowerlessFiniteClosureSyntax.finite_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω f := by
  obtain ⟨g, hg, hCover, hInj⟩ := exists_l hℳ hf
  exact ⟨k, hk, g, hg, hCover, hInj⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFunctionEnumeration
