import BMSConstructibleBridge.PowerlessCollapseSyntax
import BMSConstructibleBridge.PowerlessTraceUnique

/-!
# 内部良序坍缩的局部唯一性

用纯取值一致公式的内部良序归纳。只比较初段上的实际集合函数，
不要求所给模型的关系外部良基，也不选择宿主序数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCollapseUnique

open Logic FirstOrder ThirdOrderSemantics PowerlessInitialSegment PowerlessCollapseSyntax

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem compatible_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A R f g D E B C : carrier_l ℳ} (hR : wellOrder_l A R)
    (hD : initial_l D A R) (hE : initial_l E A R)
    (hf : map_l f D B) (hg : map_l g E C) (hF : collapse_l f D R) (hG : collapse_l g E R) :
    ∀ x y z, value_l f x y → value_l g x z → y = z := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 2 :=
    { bound := Fin.cases f (fun _ => g), free := fun _ => A }
  have h : ∀ x, PowerlessTraceUnique.agree_m.satisfies ((PowerlessComprehension.env_l η).pushFree x) ↔
      ∀ y z, value_l f x y → value_l g x z → y = z := fun x => PowerlessTraceUnique.agree_formula_l _
  have h₀ := PowerlessWellOrder.induction_l hℳ PowerlessTraceUnique.agree_m η hR
    (fun x _ h₁ => (h x).mpr (by
      intro y z hy hz
      have hx := (PowerlessFunction.value_mem_l hℳ hf hy).1
      have hx₀ := (PowerlessFunction.value_mem_l hℳ hg hz).1
      apply (PowerlessTheory.ext_l hℳ).eq_of_same_members
      intro w
      constructor
      · intro hw
        obtain ⟨k, hk, h₂, h₃⟩ := (hF x y hy w).mp hw
        have hk₀ := hD.1 k hk
        have hk₁ := hE.2 x hx₀ k hk₀ h₂
        obtain ⟨v, hv, _⟩ := hg.2 k hk₁
        have h₄ := (h k).mp (h₁ k hk₀ h₂) w v h₃ hv.2
        exact (hG x z hz w).mpr ⟨k, hk₁, h₂, h₄.symm ▸ hv.2⟩
      · intro hw
        obtain ⟨k, hk, h₂, h₃⟩ := (hG x z hz w).mp hw
        have hk₀ := hE.1 k hk
        have hk₁ := hD.2 x hx k hk₀ h₂
        obtain ⟨v, hv, _⟩ := hf.2 k hk₁
        have h₄ := (h k).mp (h₁ k hk₀ h₂) v w hv.2 h₃
        exact (hF x y hy w).mpr ⟨k, hk₁, h₂, h₄ ▸ hv.2⟩))
  intro x y z hy hz
  have hx := hD.1 x (PowerlessFunction.value_mem_l hℳ hf hy).1
  exact (h x).mp (h₀ x hx) y z hy hz

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A R f g D B C : carrier_l ℳ} (hR : wellOrder_l A R) (hD : initial_l D A R)
    (hf : map_l f D B) (hg : map_l g D C) (hF : collapse_l f D R) (hG : collapse_l g D R) : f = g := by
  have h := compatible_l hℳ hR hD hD hf hg hF hG
  apply PowerlessFunction.ext_l hℳ hf hg
  intro x hx y
  constructor
  · intro hy
    obtain ⟨z, hz, _⟩ := hg.2 x hx
    exact (h x y z hy hz.2).symm ▸ hz.2
  · intro hy
    obtain ⟨z, hz, _⟩ := hf.2 x hx
    exact h x z y hz.2 hy ▸ hz.2

theorem stage_unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A R x f g : carrier_l ℳ} (hR : wellOrder_l A R) (hx : member_l ℳ x A)
    (hf : stage_l f x R A) (hg : stage_l g x R A) : f = g := by
  obtain ⟨D, B, hD, hf, hF⟩ := hf
  obtain ⟨E, C, hE, hg, hG⟩ := hg
  have h := PowerlessInitialSegment.unique_l hℳ hD hE
  subst E
  exact unique_l hℳ hR (initial_segment_l hR hx hD) hf hg hF hG

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCollapseUnique
