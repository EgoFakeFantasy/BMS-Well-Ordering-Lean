import BMSConstructibleBridge.PowerlessWellRecursionSyntax
import BMSConstructibleBridge.PowerlessTraceUnique

/-! # 前史递归的初段相容性与唯一性 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessWellRecursionUnique

open Logic FirstOrder ThirdOrderSemantics PowerlessInitialSegment PowerlessWellRecursionSyntax

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ : SortContext ℒ}

theorem compatible_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (φ : Formula ℒ [] (.set :: .set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (h : ∀ x H y z, rule_l φ η x H y → rule_l φ η x H z → y = z)
    {A R f g D E B C : carrier_l ℳ} (hR : wellOrder_l A R)
    (hD : initial_l D A R) (hE : initial_l E A R) (hf : map_l f D B) (hg : map_l g E C)
    (hF : solution_l φ η f R) (hG : solution_l φ η g R) :
    ∀ x y z, value_l f x y → value_l g x z → y = z := by
  let θ : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 2 :=
    { bound := Fin.cases f (fun _ => g), free := fun _ => A }
  have h₀ : ∀ x, PowerlessTraceUnique.agree_m.satisfies ((PowerlessComprehension.env_l θ).pushFree x) ↔
      ∀ y z, value_l f x y → value_l g x z → y = z := fun x => PowerlessTraceUnique.agree_formula_l _
  have h₁ := PowerlessWellOrder.induction_l hℳ PowerlessTraceUnique.agree_m θ hR
    (fun x _ h₂ => (h₀ x).mpr (by
      intro y z hy hz
      have hx := (PowerlessFunction.value_mem_l hℳ hf hy).1
      have hx₀ := (PowerlessFunction.value_mem_l hℳ hg hz).1
      obtain ⟨H, hH, h₃⟩ := hF x y hy
      obtain ⟨K, hK, h₄⟩ := hG x z hz
      have h₅ : ∀ k v, value_l R k x → (value_l f k v ↔ value_l g k v) := by
        intro k v hk
        constructor
        · intro hv
          have hk₀ := hD.1 k (PowerlessFunction.value_mem_l hℳ hf hv).1
          obtain ⟨w, hw, _⟩ := hg.2 k (hE.2 x hx₀ k hk₀ hk)
          exact ((h₀ k).mp (h₂ k hk₀ hk) v w hv hw.2).symm ▸ hw.2
        · intro hv
          have hk₀ := hE.1 k (PowerlessFunction.value_mem_l hℳ hg hv).1
          obtain ⟨w, hw, _⟩ := hf.2 k (hD.2 x hx k hk₀ hk)
          exact (h₀ k).mp (h₂ k hk₀ hk) w v hw.2 hv ▸ hw.2
      have h₆ := PowerlessHistory.unique_l hℳ (PowerlessHistory.transfer_l hH h₅) hK
      subst K
      exact h x H y z h₃ h₄))
  intro x y z hy hz
  exact (h₀ x).mp (h₁ x (hD.1 x (PowerlessFunction.value_mem_l hℳ hf hy).1)) y z hy hz

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (φ : Formula ℒ [] (.set :: .set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (h : ∀ x H y z, rule_l φ η x H y → rule_l φ η x H z → y = z)
    {A R f g D B C : carrier_l ℳ} (hR : wellOrder_l A R) (hD : initial_l D A R)
    (hf : map_l f D B) (hg : map_l g D C) (hF : solution_l φ η f R) (hG : solution_l φ η g R) : f = g := by
  have h₀ := compatible_l hℳ φ η h hR hD hD hf hg hF hG
  apply PowerlessFunction.ext_l hℳ hf hg
  intro x hx y
  constructor
  · intro hy
    obtain ⟨z, hz, _⟩ := hg.2 x hx
    exact (h₀ x y z hy hz.2).symm ▸ hz.2
  · intro hy
    obtain ⟨z, hz, _⟩ := hf.2 x hx
    exact h₀ x z y hz.2 hy ▸ hz.2

theorem stage_unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (φ : Formula ℒ [] (.set :: .set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (h : ∀ x H y z, rule_l φ η x H y → rule_l φ η x H z → y = z)
    {A R x f g : carrier_l ℳ} (hR : wellOrder_l A R) (hx : member_l ℳ x A)
    (hf : stage_l φ η f x R A) (hg : stage_l φ η g x R A) : f = g := by
  obtain ⟨D, B, hD, hf, hF⟩ := hf
  obtain ⟨E, C, hE, hg, hG⟩ := hg
  have h₀ := PowerlessInitialSegment.unique_l hℳ hD hE
  subst E
  exact unique_l hℳ φ η h hR (initial_segment_l hR hx hD) hf hg hF hG

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessWellRecursionUnique
