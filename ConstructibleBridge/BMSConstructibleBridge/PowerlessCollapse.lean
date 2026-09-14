import BMSConstructibleBridge.PowerlessCollapseUnion
import BMSConstructibleBridge.PowerlessCollapseExtension

/-!
# 内部良序坍缩函数的存在

按内部良序对实际局部坍缩公式归纳，收集前驱处的唯一解，取并后添上端点。
证明不依赖幂集、公理化递归、宿主良基或宿主序数；值域的序型性质另行核验。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCollapse

open Logic FirstOrder ThirdOrderSemantics PowerlessInitialSegment PowerlessCollapseSyntax

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem family_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A R C : carrier_l ℳ} (hR : wellOrder_l A R) (hC : subset_l C A)
    (h : ∀ x, member_l ℳ x C → ∃ f, stage_l f x R A) :
    ∃ H, ∀ f, member_l ℳ f H ↔ ∃ x, member_l ℳ x C ∧ stage_l f x R A := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 2 :=
    { bound := Fin.cases R (fun _ => A), free := fun _ => C }
  have h₀ : ∀ x f, stage_m.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree f) ↔
      stage_l f x R A := fun _ _ => stage_formula_l _
  obtain ⟨H, hH⟩ := PowerlessComprehension.image_l hℳ stage_m η C
    (fun x hx => by
      obtain ⟨f, hf⟩ := h x hx
      exact ⟨f, (h₀ x f).mpr hf⟩)
    (fun x hx f g hf hg => PowerlessCollapseUnique.stage_unique_l hℳ hR (hC x hx)
      ((h₀ x f).mp hf) ((h₀ x g).mp hg))
  exact ⟨H, fun f => (hH f).trans (exists_congr fun x => and_congr Iff.rfl (h₀ x f))⟩

theorem step_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A R a : carrier_l ℳ} (hR : wellOrder_l A R) (ha : member_l ℳ a A)
    (h : ∀ x, member_l ℳ x A → value_l R x a → ∃ f, stage_l f x R A) :
    ∃ f, stage_l f a R A := by
  obtain ⟨C, hC⟩ := predecessor_exists_l hℳ A R a
  have h₀ : subset_l C A := fun x hx => ((hC x).mp hx).1
  have h₁ : ∀ x, member_l ℳ x C → ∃ f, stage_l f x R A :=
    fun x hx => h x ((hC x).mp hx).1 ((hC x).mp hx).2
  obtain ⟨H, hH⟩ := family_l hℳ hR h₀ h₁
  obtain ⟨f, B, hf, hF⟩ := PowerlessCollapseUnion.exists_l hℳ hR h₀
    (fun g hg => by
      obtain ⟨x, hx, D, E, hD, hG, h₂⟩ := (hH g).mp hg
      have hx₀ := (hC x).mp hx
      exact ⟨D, E, initial_segment_l hR hx₀.1 hD,
        below_l hR ha hx₀.1 hx₀.2 hD hC, hG, h₂⟩)
    (fun x hx => by
      obtain ⟨g, hg⟩ := h₁ x hx
      have h₂ := (hH g).mpr ⟨x, hx, hg⟩
      obtain ⟨D, E, hD, hG, _⟩ := hg
      obtain ⟨y, hy, _⟩ := hG.2 x ((hD x).mpr ⟨h₀ x hx, Or.inr rfl⟩)
      exact ⟨g, h₂, y, hy.2⟩)
  exact PowerlessCollapseExtension.exists_l hℳ hR ha hC hf hF

theorem stage_exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A R : carrier_l ℳ} (hR : wellOrder_l A R) :
    ∀ x, member_l ℳ x A → ∃ f, stage_l f x R A := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 2 :=
    { bound := Fin.cases R (fun _ => A), free := fun _ => A }
  have h : ∀ x, (stage_m.existsFreeTop SetTheory.SetSort.set).satisfies ((PowerlessComprehension.env_l η).pushFree x) ↔
      ∃ f, stage_l f x R A := by
    intro x
    rw [Formula.satisfies_existsFreeTop]
    exact exists_congr fun _ => stage_formula_l _
  have h₀ := PowerlessWellOrder.induction_l hℳ (stage_m.existsFreeTop SetTheory.SetSort.set) η hR
    (fun x hx h₁ => (h x).mpr (step_l hℳ hR hx (fun y hy h₂ => (h y).mp (h₁ y hy h₂))))
  exact fun x hx => (h x).mp (h₀ x hx)

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A R : carrier_l ℳ} (hR : wellOrder_l A R) :
    ∃ f B, map_l f A B ∧ collapse_l f A R := by
  have h := stage_exists_l hℳ hR
  obtain ⟨H, hH⟩ := family_l hℳ hR (fun _ hx => hx) h
  exact PowerlessCollapseUnion.exists_l hℳ hR (fun _ hx => hx)
    (fun g hg => by
      obtain ⟨x, hx, D, B, hD, hG, h₀⟩ := (hH g).mp hg
      have h₁ := initial_segment_l hR hx hD
      exact ⟨D, B, h₁, h₁.1, hG, h₀⟩)
    (fun x hx => by
      obtain ⟨g, hg⟩ := h x hx
      have h₀ := (hH g).mpr ⟨x, hx, hg⟩
      obtain ⟨D, B, hD, hG, _⟩ := hg
      obtain ⟨y, hy, _⟩ := hG.2 x ((hD x).mpr ⟨hx, Or.inr rfl⟩)
      exact ⟨g, h₀, y, hy.2⟩)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCollapse
