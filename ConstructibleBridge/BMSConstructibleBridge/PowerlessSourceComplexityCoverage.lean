import BMSConstructibleBridge.PowerlessSourceComplexityTotal
import BMSConstructibleBridge.PowerlessSourceRealization
import BMSConstructibleBridge.PowerlessAssignmentPadding
import BMSConstructibleBridge.PowerlessEvaluationOperator

/-!
# 一般复杂度界的实际数码与统一参数覆盖

消费已在域与参数之前固定的内部层号编译界，保留同一码的证书和语义。
同一参数图与数码覆盖全部追加元素；输出切片保留实际来源。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceComplexityCoverage

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem compilation_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ n S F : carrier_l ℳ} (hω : omega_l ω)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F)
    (hS : ∀ f, member_l ℳ f S ↔ ∃ m, member_l ℳ m ω ∧ map_l f m A)
    (hA : ∃ a, member_l ℳ a A) {Γ Δ : SortContext ℒ}
    {φ : Formula ℒ Γ Δ} {p : Formula.LevyPolarity}
    (hφ : PowerlessSourceComplexity.bound_l ω e T t₁ t₂ t₃ n p φ)
    (ξ : Env ℳ Γ Δ) {k : carrier_l ℳ} (hk : member_l ℳ k ω)
    (hξ : PowerlessSourceEnvironment.bounded_l ξ k) :
    ∃ c N, member_l ℳ c ω ∧ member_l ℳ N ω ∧ subset_l k N ∧
      PowerlessLevyCertificate.class_l ω e T t₁ t₂ t₃ c n (PowerlessSourcePolarity.code_l e t₁ p) ∧
      PowerlessSourceSpecification.spec_l ω A F c N hA ξ φ := by
  obtain ⟨J, hJ, hkJ, h⟩ := hφ A S F hF hS hA k hk
  obtain ⟨M, hM⟩ := PowerlessNatural.successor_exists_l hℳ J
  obtain ⟨c, hc, hC, h₀⟩ := h J hJ (fun _ hx => hx) M hM ξ (fun t => Or.inl (hξ t))
  exact ⟨c, M, hc, PowerlessNatural.successor_mem_l hℳ hω hJ hM,
    (fun x hx => (hM x).mpr (Or.inl (hkJ x hx))), hC, h₀⟩

theorem point_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ n S F : carrier_l ℳ} (hω : omega_l ω)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F)
    (hS : ∀ f, member_l ℳ f S ↔ ∃ m, member_l ℳ m ω ∧ map_l f m A)
    {hA : ∃ a, member_l ℳ a A} {Γ Δ : SortContext ℒ}
    {φ : Formula ℒ (.set :: Γ) Δ} {p : Formula.LevyPolarity}
    (hφ : PowerlessSourceComplexity.bound_l ω e T t₁ t₂ t₃ n p φ) (η : Env (structure_l A hA) Γ Δ) :
    ∃ c g, member_l ℳ c ω ∧ PowerlessLevyCertificate.class_l ω e T t₁ t₂ t₃ c n (PowerlessSourcePolarity.code_l e t₁ p) ∧ member_l ℳ g S ∧ ∀ x : type_l A,
      PowerlessEvaluationSlice.point_l ω A F c g x.val ↔ Formula.satisfies (η.pushBound x) φ := by
  obtain ⟨k, f, ξ, hk, hf, hξ, hη⟩ := PowerlessSourceRealization.exists_l hℳ hω η
  obtain ⟨J, hJ, hkJ, h⟩ := hφ A S F hF hS hA k hk
  obtain ⟨M, hM⟩ := PowerlessNatural.successor_exists_l hℳ J
  have hMω := PowerlessNatural.successor_mem_l hℳ hω hJ hM
  obtain ⟨c, hc, hC, h₀⟩ := h J hJ (fun _ hx => hx) M hM (ξ.pushBound J)
    (PowerlessSourceSlots.endpoint_l hξ)
  obtain ⟨a, ha⟩ := hA
  obtain ⟨g, hg, _, hfg⟩ := PowerlessAssignmentPadding.exists_l hℳ hf hkJ ha
  have h₁ : PowerlessSourceEnvironment.represents_l ξ η g := fun t => hfg _ _ (hη t)
  refine ⟨c, g, hc, hC, (hS g).mpr ⟨J, hJ, hg⟩, ?_⟩
  intro x
  constructor
  · rintro ⟨n, _, hn, q, hq, h₂⟩
    have h₃ := PowerlessAssignmentUpdate.length_unique_l hℳ hn hg
    subst n
    exact (h₀ M hMω (fun _ hx => hx) q
      (PowerlessAppendGraph.map_l hℳ hg x.property hM hq) (η.pushBound x)
      (PowerlessSourceExtension.bound_l hℳ h₁ x hq)).mp h₂
  · intro hx
    obtain ⟨q, hq⟩ := PowerlessAppendGraph.exists_l hℳ g J x.val
    exact ⟨J, hJ, hg, q, hq, (h₀ M hMω (fun _ hy => hy) q
      (PowerlessAppendGraph.map_l hℳ hg x.property hM hq) (η.pushBound x)
      (PowerlessSourceExtension.bound_l hℳ h₁ x hq)).mpr hx⟩

theorem family_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ n S F D : carrier_l ℳ} (hω : omega_l ω)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F)
    (hS : ∀ f, member_l ℳ f S ↔ ∃ m, member_l ℳ m ω ∧ map_l f m A)
    (hD : PowerlessEvaluationFamily.family_l ω A F S D)
    {hA : ∃ a, member_l ℳ a A} {Γ Δ : SortContext ℒ}
    {φ : Formula ℒ (.set :: Γ) Δ} {p : Formula.LevyPolarity}
    (hφ : PowerlessSourceComplexity.bound_l ω e T t₁ t₂ t₃ n p φ) (η : Env (structure_l A hA) Γ Δ) :
    ∃ c g B, member_l ℳ c ω ∧ PowerlessLevyCertificate.class_l ω e T t₁ t₂ t₃ c n (PowerlessSourcePolarity.code_l e t₁ p) ∧
      member_l ℳ g S ∧ member_l ℳ B D ∧ PowerlessEvaluationSlice.slice_l ω A F c g B ∧ ∀ x, member_l ℳ x B ↔
      ∃ hx : member_l ℳ x A, Formula.satisfies (η.pushBound ⟨x, hx⟩) φ := by
  obtain ⟨c, g, hc, hC, hg, h⟩ := point_l hℳ hω hF hS hφ η
  obtain ⟨B, hB⟩ := PowerlessEvaluationSlice.exists_l hℳ ω A F c g
  refine ⟨c, g, B, hc, hC, hg, (hD B).mpr ⟨c, hc, g, hg, hB⟩, hB, ?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨hx, h₀⟩ := (hB x).mp hx
    exact ⟨hx, (h ⟨x, hx⟩).mp h₀⟩
  · rintro ⟨hx, h₀⟩
    exact (hB x).mpr ⟨hx, (h ⟨x, hx⟩).mpr h₀⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceComplexityCoverage
