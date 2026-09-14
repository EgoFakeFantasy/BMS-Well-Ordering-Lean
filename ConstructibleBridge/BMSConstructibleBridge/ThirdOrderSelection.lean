import BMSConstructibleBridge.PowerlessCollect
import BMSConstructibleBridge.PowerlessWellOrder
import BMSConstructibleBridge.PowerlessFunction

/-!
# 三阶工作背景中的可定义选择

对任意给定纯公式在集合域上的总关系，先收集共同见证界，再良序化此界，
选取各纤维的最小见证。结果是模型内部集合函数，不是宿主选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderSelection

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def least_m {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ)) :
    Formula ℒ [] (.set :: .set :: .set :: .set :: Γ) :=
  let σ : Substitution ℒ [] (.set :: .set :: Γ) [] (.set :: .set :: .set :: .set :: Γ) :=
    .map (fun v => nomatch v) (fun {s} v => match s, v with
      | .set, .here => .fvar .here
      | .set, .there .here => .fvar (.there .here)
      | .set, .there (.there v) => .fvar (.there (.there (.there (.there v)))))
  let τ : Substitution ℒ [] (.set :: .set :: Γ) [.set] (.set :: .set :: .set :: .set :: Γ) :=
    .map (fun v => nomatch v) (fun {s} v => match s, v with
      | .set, .here => .bvar .here
      | .set, .there .here => .fvar (.there .here)
      | .set, .there (.there v) => .fvar (.there (.there (.there (.there v)))))
  .conj (SecondOrderObjectSyntax.member_m (.fvar .here) (.fvar (.there (.there (.there .here)))))
    (.conj (φ.substitute σ) (.forallE .set (.imp
      (SecondOrderObjectSyntax.member_m (.bvar .here) (.fvar (.there (.there (.there .here)))))
      (.imp (SecondOrderObjectSyntax.value_m (.fvar (.there (.there .here))) (.bvar .here) (.fvar .here))
        (.neg (φ.substitute τ))))))

def least_l {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (R B x y : carrier_l ℳ) : Prop :=
  member_l ℳ y B ∧ φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) ∧
    ∀ z, member_l ℳ z B → value_l R z y →
      ¬φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree z)

theorem least_formula_l {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (R B x y : carrier_l ℳ) :
    (least_m φ).satisfies (((((PowerlessComprehension.env_l η).pushFree B).pushFree R).pushFree x).pushFree y) ↔
      least_l φ η R B x y := by
  simp only [least_m, least_l, Formula.satisfies, Formula.satisfies_substitute,
    value_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval]
  apply and_congr Iff.rfl
  apply and_congr
  · apply Iff.of_eq
    apply congrArg (fun η => φ.satisfies η)
    apply Env.ext
    · intro s v
      nomatch v
    · intro s v
      match s, v with
      | .set, .here => rfl
      | .set, .there .here => rfl
      | .set, .there (.there v) => rfl
  · apply forall_congr'
    intro z
    apply imp_congr_right
    intro _
    apply imp_congr_right
    intro _
    apply not_congr
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

/-- 可定义选择仅用核心收集及集合良序化，不用实数集合或全集规模界。 -/
theorem of_choice_l (h₀ : Theory.Models ℳ PowerlessTheory.theory_m)
    (hC : ∀ B : carrier_l ℳ, ∃ R, wellOrder_l B R)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (A : carrier_l ℳ)
    (h : ∀ x, member_l ℳ x A → ∃ y, φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y)) :
    ∃ f D, map_l f A D ∧ ∀ x y, value_l f x y →
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) := by
  obtain ⟨B, hB⟩ := PowerlessCollect.exists_l h₀ φ η A h
  obtain ⟨R, hR⟩ := hC B
  have h₁ : ∀ x y, (least_m φ).satisfies
      (((PowerlessComprehension.env_l ((η.push B).push R)).pushFree x).pushFree y) ↔ least_l φ η R B x y := by
    intro x y
    rw [PowerlessComprehension.env_push_l (Γ := .set :: Γ) (η.push B) R,
      PowerlessComprehension.env_push_l (Γ := Γ) η B]
    exact least_formula_l φ η R B x y
  obtain ⟨f, D, hf, _, hV⟩ := PowerlessMapping.exists_l h₀ (least_m φ) ((η.push B).push R) A
    (fun x hx => by
      have h₂ : ∃ y, member_l ℳ y B ∧
          φ.satisfies ((PowerlessComprehension.env_l (η.push x)).pushFree y) := by
        rw [PowerlessComprehension.env_push_l (Γ := Γ) η x]
        exact hB x hx
      obtain ⟨y, hy, h₃, h₄⟩ := PowerlessWellOrder.minimum_l h₀ φ (η.push x) hR h₂
      refine ⟨y, (h₁ x y).mpr ⟨hy, ?_, ?_⟩⟩
      · rw [PowerlessComprehension.env_push_l (Γ := Γ) η x] at h₃
        exact h₃
      · intro z hz hzy hφ
        apply h₄ z hz ?_ hzy
        rw [PowerlessComprehension.env_push_l (Γ := Γ) η x]
        exact hφ)
    (fun x _ y z hy hz => by
      obtain ⟨hy, hY, h₂⟩ := (h₁ x y).mp hy
      obtain ⟨hz, hZ, h₃⟩ := (h₁ x z).mp hz
      rcases hR.2.2.1 y z ⟨hy, hz⟩ with h₄ | h₄ | h₄
      · exact (h₃ y hy h₄ hY).elim
      · exact h₄
      · exact (h₂ z hz h₄ hZ).elim)
  refine ⟨f, D, hf, fun x y hy => ?_⟩
  exact ((h₁ x y).mp ((hV x (PowerlessFunction.value_mem_l h₀ hf hy).1 y).mp hy)).2.1

theorem exists_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (A : carrier_l ℳ)
    (h : ∀ x, member_l ℳ x A → ∃ y, φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y)) :
    ∃ f D, map_l f A D ∧ ∀ x y, value_l f x y →
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) :=
  of_choice_l (ThirdOrderTheory.core_l hℳ) (ThirdOrderSemantics.choice_l hℳ) φ η A h

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderSelection
