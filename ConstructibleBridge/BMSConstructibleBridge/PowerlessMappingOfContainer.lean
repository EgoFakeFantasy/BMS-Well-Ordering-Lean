import BMSConstructibleBridge.PowerlessMapping
import BMSConstructibleBridge.PowerlessBoundedWitness

/-!
# 值与序对各有实际容器时的集合函数图

`PowerlessMapping.exists_l` 有两处 `PowerlessComprehension.image_l`，而同一条
`Mapping.exists_l → image_l → PowerlessImage.exists_l` 是层次机制里所有收集入口的共同尾段。
本模块把这两处需求精确改写成两个容器假设：像落在 `D` 内、Kuratowski 序对落在 `G` 内。
结论与原 `exists_l` 逐字同形，证明体只消费分离与既有配对引理。
它不声称这样的容器在无幂集核心内总存在，也不替代原 `exists_l`。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessMappingOfContainer

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) {Γ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (A D G : carrier_l ℳ)
    (hb : ∀ x, member_l ℳ x A → ∀ y,
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) → member_l ℳ y D)
    (hg : ∀ x, member_l ℳ x A → ∀ y p,
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) →
        ordered_l x y p → member_l ℳ p G)
    (h : ∀ x, member_l ℳ x A → ∃ y,
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y))
    (h₁ : ∀ x, member_l ℳ x A → ∀ y z,
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) →
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree z) → y = z) :
    ∃ f B, map_l f A B ∧
      (∀ y, member_l ℳ y B ↔ ∃ x, member_l ℳ x A ∧
        φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y)) ∧
      ∀ x, member_l ℳ x A → ∀ y, value_l f x y ↔
        φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) := by
  obtain ⟨B, hB⟩ := PowerlessBoundedWitness.image_of_container_l hℳ φ η A D hb
  have hgb : ∀ x, member_l ℳ x A → ∀ p,
      (PowerlessMapping.graph_m φ).satisfies
        (((PowerlessComprehension.env_l η).pushFree x).pushFree p) → member_l ℳ p G := by
    intro x hx p hp
    obtain ⟨y, hy, hp⟩ := (PowerlessMapping.graph_formula_l φ η x p).mp hp
    exact hg x hx y p hy hp
  obtain ⟨f, hf⟩ := PowerlessBoundedWitness.image_of_container_l hℳ
    (PowerlessMapping.graph_m φ) η A G hgb
  have hF : ∀ p, member_l ℳ p f ↔ ∃ x, member_l ℳ x A ∧ ∃ y,
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) ∧ ordered_l x y p :=
    fun p => (hf p).trans (exists_congr fun x =>
      and_congr Iff.rfl (PowerlessMapping.graph_formula_l φ η x p))
  have hV : ∀ x, member_l ℳ x A → ∀ y, value_l f x y ↔
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) := by
    intro x hx y
    constructor
    · rintro ⟨p, hp, h₄⟩
      obtain ⟨z, _, w, hw, h₅⟩ := (hF p).mp hp
      obtain ⟨h₆, h₇⟩ := (PowerlessBasic.ordered_eq_l hℳ h₄ h₅).mp rfl
      subst z
      subst w
      exact hw
    · intro hy
      obtain ⟨p, hp⟩ := PowerlessBasic.ordered_exists_l hℳ x y
      exact ⟨p, (hF p).mpr ⟨x, hx, y, hy, hp⟩, hp⟩
  refine ⟨f, B, ⟨?_, ?_⟩, hB, hV⟩
  · intro p hp
    obtain ⟨x, hx, y, hy, h₄⟩ := (hF p).mp hp
    exact ⟨x, y, hx, (hB y).mpr ⟨x, hx, hy⟩, h₄⟩
  · intro x hx
    obtain ⟨y, hy⟩ := h x hx
    refine ⟨y, ⟨(hB y).mpr ⟨x, hx, hy⟩, (hV x hx y).mpr hy⟩, ?_⟩
    intro z hz
    exact h₁ x hx z y ((hV x hx z).mp hz.2) hy

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessMappingOfContainer
