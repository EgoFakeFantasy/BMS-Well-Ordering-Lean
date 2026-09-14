import BMSConstructibleBridge.PowerlessSourceInclusion
import BMSConstructibleBridge.PowerlessSourceComplexityCoverage
import BMSConstructibleBridge.PowerlessLevyWitness
import BMSConstructibleBridge.PowerlessSourceRealization
import BMSConstructibleBridge.PowerlessAssignmentPadding

/-!
# 有限正层查询一致给出的原源存在见证

只在上域编译源子式。其 Σ 证书和指定存在节点在同一层内，
实际见证准则先取小域元素，再由上域的同一编译规格读取真值。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceLevyWitness

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure PowerlessSourceEnvironment

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A U t₁ t₂ t₃ S R F G n : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T U t₁ t₂ t₃ S F)
    (hG : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ R G)
    (hS : ∀ f, ThirdOrderSemantics.member_l ℳ f S ↔ ∃ m, ThirdOrderSemantics.member_l ℳ m ω ∧ map_l f m U)
    (hA : ∃ a, ThirdOrderSemantics.member_l ℳ a A) (hU : ∃ a, ThirdOrderSemantics.member_l ℳ a U)
    (hAU : subset_l A U) (hC : PowerlessLevyAgreement.agreement_l ω e T t₁ t₂ t₃ A F G n)
    (he : ThirdOrderSemantics.member_l ℳ e n)
    {Γ Δ : SortContext ℒ} (φ : Formula ℒ (.set :: Γ) Δ)
    (hφ : PowerlessSourceComplexity.bound_l ω e T t₁ t₂ t₃ n .sigma φ) (η : Env (structure_l A hA) Γ Δ)
    (h : ∃ x : type_l U, Formula.satisfies ((PowerlessSourceInclusion.env_l (hU := hU) hAU η).pushBound x) φ) :
    ∃ x : type_l A, Formula.satisfies ((PowerlessSourceInclusion.env_l (hU := hU) hAU η).pushBound
      (PowerlessSourceInclusion.inclusion_l hAU x)) φ := by
  obtain ⟨k, f, ξ, hk, hf, hξ, hη⟩ := PowerlessSourceRealization.exists_l hℳ hω η
  obtain ⟨l, hl⟩ := PowerlessNatural.successor_exists_l hℳ k
  obtain ⟨b, N, _, hN, hlN, hB, h₀⟩ := PowerlessSourceComplexityCoverage.compilation_l hℳ hω hF hS hU hφ
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
  obtain ⟨n, hn, hg₁, _, a, ha, r, hr, h₄, h₅⟩ :=
    PowerlessLevyWitness.exists_l hℳ hω ht hT hF hG hS hAU hC he hk hB ⟨N, hN, hg⟩ h₃
  have h₆ := PowerlessAssignmentUpdate.length_unique_l hℳ hg₁ hg₀
  subst n
  have hr₀ := PowerlessFunction.range_l hℳ hr
    (fun _ y hy => hAU y (PowerlessFunction.value_mem_l hℳ hr hy).2)
  exact ⟨⟨a, ha⟩, (h₀ N hn (fun _ hy => hy) r hr₀ _
    (PowerlessSourceEnvironment.update_l (PowerlessSourceEnvironment.fresh_l hℳ hξ) hη₁
      (PowerlessSourceInclusion.inclusion_l hAU ⟨a, ha⟩) h₄)).mp h₅⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceLevyWitness
