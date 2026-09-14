import BMSConstructibleBridge.PowerlessBasic
import BMSConstructibleBridge.PowerlessComprehension

/-!
# 纯定义的实际集合函数图

从给定集合上的总唯一纯关系，同时构造精确值域与 Kuratowski 函数图。
这是内部递归需要的集合函数接口，不把宿主选取的函数当成模型对象。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessMapping

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def graph_m {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ)) :
    Formula ℒ [] (.set :: .set :: Γ) :=
  let σ : Substitution ℒ [] (.set :: .set :: Γ) [.set] (.set :: .set :: Γ) :=
    .map (fun v => nomatch v) (fun {s} v => match s, v with
      | .set, .here => .bvar .here
      | .set, .there .here => .fvar (.there .here)
      | .set, .there (.there v) => .fvar (.there (.there v)))
  .existsE .set (.conj (φ.substitute σ)
    (SecondOrderObjectSyntax.ordered_m (.fvar (.there .here)) (.bvar .here) (.fvar .here)))

theorem graph_formula_l {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (x p : carrier_l ℳ) :
    (graph_m φ).satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree p) ↔
      ∃ y, φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) ∧ ordered_l x y p := by
  simp only [graph_m, Formula.satisfies, Formula.satisfies_substitute, ordered_formula_l]
  apply exists_congr
  intro y
  apply and_congr ?_ Iff.rfl
  apply Iff.of_eq
  apply congrArg (fun η => φ.satisfies η)
  apply Env.ext
  · intro s v
    nomatch v
  · intro s v
    match s, v with
    | .set, .here => rfl
    | .set, .there .here => rfl
    | .set, .there (.there v) => rfl

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) {Γ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (A : carrier_l ℳ)
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
  obtain ⟨B, hB⟩ := PowerlessComprehension.image_l hℳ φ η A h h₁
  have h₂ : ∀ x, member_l ℳ x A → ∃ p,
      (graph_m φ).satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree p) := by
    intro x hx
    obtain ⟨y, hy⟩ := h x hx
    obtain ⟨p, hp⟩ := PowerlessBasic.ordered_exists_l hℳ x y
    exact ⟨p, (graph_formula_l φ η x p).mpr ⟨y, hy, hp⟩⟩
  have h₃ : ∀ x, member_l ℳ x A → ∀ p q,
      (graph_m φ).satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree p) →
      (graph_m φ).satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree q) → p = q := by
    intro x hx p q hp hq
    obtain ⟨y, hy, hp⟩ := (graph_formula_l φ η x p).mp hp
    obtain ⟨z, hz, hq⟩ := (graph_formula_l φ η x q).mp hq
    have h₄ := h₁ x hx y z hy hz
    subst z
    exact PowerlessBasic.ordered_unique_l hℳ hp hq
  obtain ⟨f, hf⟩ := PowerlessComprehension.image_l hℳ (graph_m φ) η A h₂ h₃
  have hF : ∀ p, member_l ℳ p f ↔ ∃ x, member_l ℳ x A ∧ ∃ y,
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) ∧ ordered_l x y p :=
    fun p => (hf p).trans (exists_congr fun x => and_congr Iff.rfl (graph_formula_l φ η x p))
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

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessMapping
