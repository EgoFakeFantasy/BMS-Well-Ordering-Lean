import BMSConstructibleBridge.PowerlessWellRecursionUnion
import BMSConstructibleBridge.PowerlessWellRecursionExtension

/-!
# 依赖前驱图的内部良序递归

对实际局部解公式作内部良序归纳，再以收集构造全部初段解的相容并。
总唯一的一步纯算子是定理前提，不是新增公理；不要求关系外部良基。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessWellRecursion

open Logic FirstOrder ThirdOrderSemantics PowerlessInitialSegment PowerlessWellRecursionSyntax

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ : SortContext ℒ}

theorem family_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (φ : Formula ℒ [] (.set :: .set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (h : ∀ x H y z, rule_l φ η x H y → rule_l φ η x H z → y = z)
    {A R C : carrier_l ℳ} (hR : wellOrder_l A R) (hC : subset_l C A)
    (h₀ : ∀ x, member_l ℳ x C → ∃ f, stage_l φ η f x R A) :
    ∃ H, ∀ f, member_l ℳ f H ↔ ∃ x, member_l ℳ x C ∧ stage_l φ η f x R A := by
  let θ : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) (.set :: .set :: Γ).length :=
    (η.push A).push R
  have h₁ : ∀ x f, (stage_m φ).satisfies (((PowerlessComprehension.env_l θ).pushFree x).pushFree f) ↔
      stage_l φ η f x R A := by
    intro x f
    dsimp only [θ]
    rw [PowerlessComprehension.env_push_l (Γ := .set :: Γ), PowerlessComprehension.env_push_l (Γ := Γ)]
    exact stage_formula_l φ η f x R A
  obtain ⟨H, hH⟩ := PowerlessComprehension.image_l hℳ (stage_m φ) θ C
    (fun x hx => (h₀ x hx).imp fun f hf => (h₁ x f).mpr hf)
    (fun x hx f g hf hg => PowerlessWellRecursionUnique.stage_unique_l hℳ φ η h hR (hC x hx)
      ((h₁ x f).mp hf) ((h₁ x g).mp hg))
  exact ⟨H, fun f => (hH f).trans (exists_congr fun x => and_congr Iff.rfl (h₁ x f))⟩

theorem step_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (φ : Formula ℒ [] (.set :: .set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (h : ∀ x H y z, rule_l φ η x H y → rule_l φ η x H z → y = z)
    {A R a : carrier_l ℳ} (hR : wellOrder_l A R) (ha : member_l ℳ a A)
    (h₀ : ∀ H, ∃ y, rule_l φ η a H y)
    (h₁ : ∀ x, member_l ℳ x A → value_l R x a → ∃ f, stage_l φ η f x R A) :
    ∃ f, stage_l φ η f a R A := by
  obtain ⟨C, hC⟩ := predecessor_exists_l hℳ A R a
  have h₂ : subset_l C A := fun x hx => ((hC x).mp hx).1
  have h₃ : ∀ x, member_l ℳ x C → ∃ f, stage_l φ η f x R A :=
    fun x hx => h₁ x ((hC x).mp hx).1 ((hC x).mp hx).2
  obtain ⟨H, hH⟩ := family_l hℳ φ η h hR h₂ h₃
  obtain ⟨f, B, hf, hF⟩ := PowerlessWellRecursionUnion.exists_l hℳ φ η h hR h₂
    (fun g hg => by
      obtain ⟨x, hx, D, E, hD, hG, h₄⟩ := (hH g).mp hg
      have hx₀ := (hC x).mp hx
      exact ⟨D, E, initial_segment_l hR hx₀.1 hD,
        below_l hR ha hx₀.1 hx₀.2 hD hC, hG, h₄⟩)
    (fun x hx => by
      obtain ⟨g, hg⟩ := h₃ x hx
      have h₄ := (hH g).mpr ⟨x, hx, hg⟩
      obtain ⟨D, E, hD, hG, _⟩ := hg
      obtain ⟨y, hy, _⟩ := hG.2 x ((hD x).mpr ⟨h₂ x hx, Or.inr rfl⟩)
      exact ⟨g, h₄, y, hy.2⟩)
  exact PowerlessWellRecursionExtension.exists_l hℳ φ η hR ha hC hf hF h₀

theorem stage_exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (φ : Formula ℒ [] (.set :: .set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (h : ∀ x H y z, rule_l φ η x H y → rule_l φ η x H z → y = z)
    {A R : carrier_l ℳ} (hR : wellOrder_l A R)
    (h₀ : ∀ x, member_l ℳ x A → ∀ H, ∃ y, rule_l φ η x H y) :
    ∀ x, member_l ℳ x A → ∃ f, stage_l φ η f x R A := by
  let θ : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) (.set :: .set :: Γ).length :=
    (η.push A).push R
  have h₁ : ∀ x, ((stage_m φ).existsFreeTop SetTheory.SetSort.set).satisfies ((PowerlessComprehension.env_l θ).pushFree x) ↔
      ∃ f, stage_l φ η f x R A := by
    intro x
    rw [Formula.satisfies_existsFreeTop]
    apply exists_congr
    intro f
    dsimp only [θ]
    rw [PowerlessComprehension.env_push_l (Γ := .set :: Γ), PowerlessComprehension.env_push_l (Γ := Γ)]
    exact stage_formula_l φ η f x R A
  have h₂ := PowerlessWellOrder.induction_l hℳ ((stage_m φ).existsFreeTop SetTheory.SetSort.set) θ hR
    (fun x hx h₃ => (h₁ x).mpr (step_l hℳ φ η h hR hx (h₀ x hx)
      (fun y hy h₄ => (h₁ y).mp (h₃ y hy h₄))))
  exact fun x hx => (h₁ x).mp (h₂ x hx)

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (φ : Formula ℒ [] (.set :: .set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (h : ∀ x H y z, rule_l φ η x H y → rule_l φ η x H z → y = z)
    {A R : carrier_l ℳ} (hR : wellOrder_l A R)
    (h₀ : ∀ x, member_l ℳ x A → ∀ H, ∃ y, rule_l φ η x H y) :
    ∃ f B, map_l f A B ∧ solution_l φ η f R := by
  have h₁ := stage_exists_l hℳ φ η h hR h₀
  obtain ⟨H, hH⟩ := family_l hℳ φ η h hR (fun _ hx => hx) h₁
  exact PowerlessWellRecursionUnion.exists_l hℳ φ η h hR (fun _ hx => hx)
    (fun g hg => by
      obtain ⟨x, hx, D, B, hD, hG, h₂⟩ := (hH g).mp hg
      have h₃ := initial_segment_l hR hx hD
      exact ⟨D, B, h₃, h₃.1, hG, h₂⟩)
    (fun x hx => by
      obtain ⟨g, hg⟩ := h₁ x hx
      have h₂ := (hH g).mpr ⟨x, hx, hg⟩
      obtain ⟨D, B, hD, hG, _⟩ := hg
      obtain ⟨y, hy, _⟩ := hG.2 x ((hD x).mpr ⟨hx, Or.inr rfl⟩)
      exact ⟨g, h₂, y, hy.2⟩)

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (φ : Formula ℒ [] (.set :: .set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (h : ∀ x H y z, rule_l φ η x H y → rule_l φ η x H z → y = z)
    {A R f g B C : carrier_l ℳ} (hR : wellOrder_l A R)
    (hf : map_l f A B) (hg : map_l g A C) (hF : solution_l φ η f R) (hG : solution_l φ η g R) : f = g :=
  PowerlessWellRecursionUnique.unique_l hℳ φ η h hR ⟨fun _ hx => hx, fun _ _ _ hy _ => hy⟩ hf hg hF hG

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessWellRecursion
