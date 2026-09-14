import BMSConstructibleBridge.PowerlessWellRecursion

/-! # 内部良序递归的纯表示与唯一函数图 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessWellRecursionPresentation

open Logic FirstOrder ThirdOrderSemantics PowerlessWellRecursionSyntax

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ : SortContext ℒ}

def recursion_l (φ : Formula ℒ [] (.set :: .set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (f A R : carrier_l ℳ) : Prop := ∃ B, map_l f A B ∧ solution_l φ η f R

/-- 自由变量依次为递归图、定义域、良序关系及原算子的参数。 -/
def recursion_m (φ : Formula ℒ [] (.set :: .set :: .set :: Γ)) :
    Formula ℒ [] (.set :: .set :: .set :: Γ) :=
  let σ : Substitution ℒ [] (.set :: .set :: Γ) [.set] (.set :: .set :: .set :: Γ) :=
    .map (fun v => nomatch v) (fun {s} v => match s, v with
      | .set, .here => .fvar .here
      | .set, .there .here => .fvar (.there (.there .here))
      | .set, .there (.there v) => .fvar (.there (.there (.there v))))
  .existsE .set (.conj (SecondOrderObjectSyntax.map_m (.fvar .here) (.fvar (.there .here)) (.bvar .here))
    ((solution_m φ).substitute σ))

theorem recursion_formula_l (φ : Formula ℒ [] (.set :: .set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (f A R : carrier_l ℳ) :
    (recursion_m φ).satisfies ((((PowerlessComprehension.env_l η).pushFree R).pushFree A).pushFree f) ↔
      recursion_l φ η f A R := by
  simp only [recursion_m, recursion_l, Formula.satisfies, map_formula_l, Formula.satisfies_substitute]
  apply exists_congr
  intro B
  apply and_congr Iff.rfl
  rw [← solution_formula_l φ η f R]
  apply Iff.of_eq
  apply congrArg (fun η => (solution_m φ).satisfies η)
  apply Env.ext
  · intro s v
    nomatch v
  · intro s v
    match s, v with
    | .set, .here => rfl
    | .set, .there .here => rfl
    | .set, .there (.there v) => rfl

theorem exists_unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (φ : Formula ℒ [] (.set :: .set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (h : ∀ x H y z, rule_l φ η x H y → rule_l φ η x H z → y = z)
    {A R : carrier_l ℳ} (hR : wellOrder_l A R)
    (h₀ : ∀ x, member_l ℳ x A → ∀ H, ∃ y, rule_l φ η x H y) :
    ∃! f, recursion_l φ η f A R := by
  obtain ⟨f, B, hf, hF⟩ := PowerlessWellRecursion.exists_l hℳ φ η h hR h₀
  refine ⟨f, ⟨B, hf, hF⟩, ?_⟩
  rintro g ⟨C, hg, hG⟩
  exact PowerlessWellRecursion.unique_l hℳ φ η h hR hg hf hG hF

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessWellRecursionPresentation
