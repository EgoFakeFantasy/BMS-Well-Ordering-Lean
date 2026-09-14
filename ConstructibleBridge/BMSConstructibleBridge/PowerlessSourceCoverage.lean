import BMSConstructibleBridge.PowerlessSourceReservation
import BMSConstructibleBridge.PowerlessSourceRealization
import BMSConstructibleBridge.PowerlessAssignmentPadding
import BMSConstructibleBridge.PowerlessEvaluationOperator

/-!
# 完整源公式的统一有限参数覆盖

同一个数码与同一个实际参数图，对所有 x∈A 同时给出末尾追加切片的
源语义。先实现参数环境，再固定预留界并填充；数码和参数图不依赖 x。
不声称任意内部数码都能反向解码为外部有限源公式。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceCoverage

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem point_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ S F : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F)
    (hS : ∀ f, member_l ℳ f S ↔ ∃ m, member_l ℳ m ω ∧ map_l f m A)
    {hA : ∃ a, member_l ℳ a A} {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ (.set :: Γ) Δ) (η : Env (structure_l A hA) Γ Δ) :
    ∃ c g, member_l ℳ c ω ∧ member_l ℳ g S ∧ ∀ x : type_l A,
      PowerlessEvaluationSlice.point_l ω A F c g x.val ↔ Formula.satisfies (η.pushBound x) φ := by
  obtain ⟨k, f, ξ, hk, hf, hξ, hη⟩ := PowerlessSourceRealization.exists_l hℳ hω η
  obtain ⟨J, hJ, hkJ, h⟩ := PowerlessSourceReservation.formula_l hℳ hω ht hT hF hS hA φ hk
  obtain ⟨M, hM⟩ := PowerlessNatural.successor_exists_l hℳ J
  have hMω := PowerlessNatural.successor_mem_l hℳ hω hJ hM
  obtain ⟨c, hc, h₀⟩ := h J hJ (fun _ hx => hx) M hM (ξ.pushBound J)
    (PowerlessSourceSlots.endpoint_l hξ)
  obtain ⟨a, ha⟩ := hA
  obtain ⟨g, hg, _, hfg⟩ := PowerlessAssignmentPadding.exists_l hℳ hf hkJ ha
  have h₁ : PowerlessSourceEnvironment.represents_l ξ η g := fun t => hfg _ _ (hη t)
  refine ⟨c, g, hc, (hS g).mpr ⟨J, hJ, hg⟩, ?_⟩
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
    {ω e T A t₁ t₂ t₃ S F D : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F)
    (hS : ∀ f, member_l ℳ f S ↔ ∃ m, member_l ℳ m ω ∧ map_l f m A)
    (hD : PowerlessEvaluationFamily.family_l ω A F S D)
    {hA : ∃ a, member_l ℳ a A} {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ (.set :: Γ) Δ) (η : Env (structure_l A hA) Γ Δ) :
    ∃ B, member_l ℳ B D ∧ ∀ x, member_l ℳ x B ↔
      ∃ hx : member_l ℳ x A, Formula.satisfies (η.pushBound ⟨x, hx⟩) φ := by
  obtain ⟨c, g, hc, hg, h⟩ := point_l hℳ hω ht hT hF hS φ η
  obtain ⟨B, hB⟩ := PowerlessEvaluationSlice.exists_l hℳ ω A F c g
  refine ⟨B, (hD B).mpr ⟨c, hc, g, hg, hB⟩, ?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨hx, h₀⟩ := (hB x).mp hx
    exact ⟨hx, (h ⟨x, hx⟩).mp h₀⟩
  · rintro ⟨hx, h₀⟩
    exact (hB x).mpr ⟨hx, (h ⟨x, hx⟩).mpr h₀⟩

theorem operator_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ D : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hD : PowerlessEvaluationOperator.operator_l ω e T t₁ t₂ t₃ A D)
    {hA : ∃ a, member_l ℳ a A} {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ (.set :: Γ) Δ) (η : Env (structure_l A hA) Γ Δ) :
    ∃ B, member_l ℳ B D ∧ ∀ x, member_l ℳ x B ↔
      ∃ hx : member_l ℳ x A, Formula.satisfies (η.pushBound ⟨x, hx⟩) φ := by
  obtain ⟨S, F, hS, hF, hD⟩ := hD
  exact family_l hℳ hω ht hT hF hS hD φ η

theorem domain_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ D : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hD : PowerlessEvaluationOperator.operator_l ω e T t₁ t₂ t₃ A D) : member_l ℳ A D := by
  classical
  by_cases hA : ∃ a, member_l ℳ a A
  · obtain ⟨B, hB, h⟩ := operator_l hℳ hω ht hT hD
      (hA := hA) (.truth : Formula ℒ [.set] []) Env.empty
    have h₀ : B = A := (PowerlessTheory.ext_l hℳ).eq_of_same_members B A (fun x =>
      (h x).trans ⟨fun ⟨hx, _⟩ => hx, fun hx => ⟨hx, trivial⟩⟩)
    exact h₀ ▸ hB
  · have h₀ : PowerlessNatural.zero_l A := fun x hx => hA ⟨x, hx⟩
    exact (PowerlessEvaluationOperator.empty_l hℳ hω hD h₀ A).mpr h₀

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceCoverage
