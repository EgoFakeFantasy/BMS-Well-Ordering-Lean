import BMSConstructibleBridge.PowerlessSourceInclusion
import BMSConstructibleBridge.PowerlessSourceCompilation
import BMSConstructibleBridge.PowerlessSourceRealization
import BMSConstructibleBridge.PowerlessAssignmentPadding
import BMSConstructibleBridge.PowerlessWitnessClosure

/-!
# 单一原域求值器给出的源存在见证准则

在小域实现参数图并填充容量，只在原域编译一次子公式。实际闭包
给回小域见证，再由同一编译规格读取源真值，避免假定两次编译同码。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceWitness

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure PowerlessSourceEnvironment

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A U t₁ t₂ t₃ S F : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T U t₁ t₂ t₃ S F)
    (hS : ∀ f, ThirdOrderSemantics.member_l ℳ f S ↔ ∃ m, ThirdOrderSemantics.member_l ℳ m ω ∧ map_l f m U)
    (hA : ∃ a, ThirdOrderSemantics.member_l ℳ a A) (hU : ∃ a, ThirdOrderSemantics.member_l ℳ a U)
    (hAU : subset_l A U) (hC : PowerlessWitnessClosure.closure_l ω U F A A)
    {Γ Δ : SortContext ℒ} (φ : Formula ℒ (.set :: Γ) Δ) (η : Env (structure_l A hA) Γ Δ)
    (h : ∃ x : type_l U, Formula.satisfies ((PowerlessSourceInclusion.env_l (hU := hU) hAU η).pushBound x) φ) :
    ∃ x : type_l A, Formula.satisfies ((PowerlessSourceInclusion.env_l (hU := hU) hAU η).pushBound
      (PowerlessSourceInclusion.inclusion_l hAU x)) φ := by
  obtain ⟨k, f, ξ, hk, hf, hξ, hη⟩ := PowerlessSourceRealization.exists_l hℳ hω η
  obtain ⟨l, hl⟩ := PowerlessNatural.successor_exists_l hℳ k
  obtain ⟨b, N, hb, hN, hlN, h₀⟩ := PowerlessSourceCompilation.formula_l hℳ hω ht hT hF hS hU φ
    (ξ.pushBound k) (PowerlessNatural.successor_mem_l hℳ hω hk hl) (PowerlessSourceEnvironment.push_l hξ hl)
  have hkN := hlN k ((hl k).mpr (Or.inr rfl))
  obtain ⟨d, hd⟩ := hA
  obtain ⟨g, hg, _, h₁⟩ := PowerlessAssignmentPadding.exists_l hℳ hf
    (fun x hx => hlN x ((hl x).mpr (Or.inl hx))) hd
  have hη₀ : represents_l ξ η g := fun t => h₁ _ _ (hη t)
  have hη₁ := PowerlessSourceInclusion.represents_l (hU := hU) hAU hη₀
  have hg₀ := PowerlessFunction.range_l hℳ hg (fun _ y hy => hAU y (PowerlessFunction.value_mem_l hℳ hg hy).2)
  obtain ⟨x, hx⟩ := h
  obtain ⟨q, hq, h₂⟩ := PowerlessAssignmentUpdate.exists_l hℳ hg₀ hkN x.property
  have h₃ : PowerlessEvaluationClause.exists_l ω U F g k b :=
    ⟨N, hN, hg₀, hkN, x.val, x.property, q, hq, h₂,
      (h₀ N hN (fun _ hy => hy) q hq _
        (PowerlessSourceEnvironment.update_l (PowerlessSourceEnvironment.fresh_l hℳ hξ) hη₁ x h₂)).mpr hx⟩
  obtain ⟨a, ha, _, n, hn, hg₁, _, r, hr, h₄, h₅⟩ := hC k b g hk hb ⟨N, hN, hg⟩ h₃
  have h₆ := PowerlessAssignmentUpdate.length_unique_l hℳ hg₁ hg₀
  subst n
  exact ⟨⟨a, ha⟩, (h₀ N hn (fun _ hy => hy) r hr _
    (PowerlessSourceEnvironment.update_l (PowerlessSourceEnvironment.fresh_l hℳ hξ) hη₁
      (PowerlessSourceInclusion.inclusion_l hAU ⟨a, ha⟩) h₄)).mp h₅⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceWitness
