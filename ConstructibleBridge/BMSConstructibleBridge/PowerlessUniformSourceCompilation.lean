import BMSConstructibleBridge.PowerlessUniformSourceSpecification
import BMSConstructibleBridge.PowerlessNaturalBounds

/-!
# 原公式的跨域统一数码与赋值长度

递归原 Formula，先构造数码和长度，再量化全部实际域、求值器及赋值。
量词在旧槽界处使用一个新槽；没有将任意内部数码反解成标准公式。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessUniformSourceCompilation

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure
open PowerlessUniformSourceSpecification (spec_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
  (hT : PowerlessTriangular.triangular_l ω e T)

include hℳ hω

theorem common_l {Γ Δ : SortContext ℒ} {ξ : Env ℳ Γ Δ} {φ ψ : Formula ℒ Γ Δ}
    {a b k N M : carrier_l ℳ} (hN : member_l ℳ N ω) (hM : member_l ℳ M ω)
    (hkN : subset_l k N) (hφ : spec_l ω e T t₁ t₂ t₃ a N ξ φ)
    (hψ : spec_l ω e T t₁ t₂ t₃ b M ξ ψ) :
    ∃ P, member_l ℳ P ω ∧ subset_l k P ∧
      spec_l ω e T t₁ t₂ t₃ a P ξ φ ∧ spec_l ω e T t₁ t₂ t₃ b P ξ ψ := by
  obtain ⟨P, hP, hNP, hMP⟩ := PowerlessNaturalBounds.upper_l hℳ hω hN hM
  exact ⟨P, hP, fun x hx => hNP x (hkN x hx),
    PowerlessUniformSourceSpecification.widen_l hφ hNP,
    PowerlessUniformSourceSpecification.widen_l hψ hMP⟩

include ht hT

theorem formula_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ Γ Δ) (ξ : Env ℳ Γ Δ)
    {k : carrier_l ℳ} (hk : member_l ℳ k ω) (hξ : PowerlessSourceEnvironment.bounded_l ξ k) :
    ∃ c N, member_l ℳ c ω ∧ member_l ℳ N ω ∧ subset_l k N ∧
      spec_l ω e T t₁ t₂ t₃ c N ξ φ := by
  match φ with
  | .falsum =>
    refine ⟨e, k, PowerlessNatural.zero_mem_l hℳ hω ht.1, hk, fun _ h => h, ?_⟩
    intro A S F hF _ _ _ _ _ f _ _ _
    exact ⟨fun h => PowerlessEvaluationLogic.zero_l hℳ hω ht hT hF f h, False.elim⟩
  | .truth =>
    obtain ⟨c, hc, h⟩ := PowerlessUniformEvaluationLogic.truth_l hℳ hω ht hT
    refine ⟨c, k, hc, hk, fun _ h => h, ?_⟩
    intro A S F hF hS _ m hm _ f hf _ _
    exact ⟨fun _ => trivial, fun _ => h hF f ((hS f).mpr ⟨m, hm, hf⟩)⟩
  | .rel .membership (.cons s (.cons t .nil)) =>
    obtain ⟨c, hc, h⟩ := PowerlessFormulaConstructor.exists_l hℳ hω ht.1 hT
      (PowerlessNatural.zero_mem_l hℳ hω ht.1)
      (PowerlessSourceEnvironment.natural_l hℳ hω hk hξ s)
      (PowerlessSourceEnvironment.natural_l hℳ hω hk hξ t)
    refine ⟨c, k, hc, hk, fun _ h => h, ?_⟩
    intro A S F hF hS _ m hm _ f hf η hη
    exact (PowerlessEvaluationEquations.member_l hℳ hω ht hT hF h f).trans
      ((and_iff_right ((hS f).mpr ⟨m, hm, hf⟩)).trans (PowerlessSourceEnvironment.member_l hℳ hf hη s t))
  | .equal (sort := .set) s t =>
    obtain ⟨c, hc, h⟩ := PowerlessFormulaConstructor.exists_l hℳ hω ht.1 hT
      (PowerlessEvaluationTags.natural_l hℳ hω ht).2.1
      (PowerlessSourceEnvironment.natural_l hℳ hω hk hξ s)
      (PowerlessSourceEnvironment.natural_l hℳ hω hk hξ t)
    refine ⟨c, k, hc, hk, fun _ h => h, ?_⟩
    intro A S F hF hS _ m hm _ f hf η hη
    exact (PowerlessEvaluationEquations.equal_l hℳ hω ht hT hF h f).trans
      ((and_iff_right ((hS f).mpr ⟨m, hm, hf⟩)).trans (PowerlessSourceEnvironment.equal_l hℳ hf hη s t))
  | .neg φ =>
    obtain ⟨b, N, hb, hN, hkN, hφ⟩ := formula_l φ ξ hk hξ
    obtain ⟨c, hc, h⟩ := PowerlessUniformSourceSpecification.negation_l hℳ hω ht hT hb hφ
    exact ⟨c, N, hc, hN, hkN, h⟩
  | .conj φ ψ =>
    obtain ⟨a, N, ha, hN, hkN, hφ⟩ := formula_l φ ξ hk hξ
    obtain ⟨b, M, hb, hM, _, hψ⟩ := formula_l ψ ξ hk hξ
    obtain ⟨P, hP, hkP, hφ, hψ⟩ := common_l hℳ hω hN hM hkN hφ hψ
    obtain ⟨c, hc, h⟩ := PowerlessUniformEvaluationLogic.conjunction_l hℳ hω ht hT ha hb
    refine ⟨c, P, hc, hP, hkP, ?_⟩
    intro A S F hF hS hA m hm hM f hf η hη
    exact (h hF f ((hS f).mpr ⟨m, hm, hf⟩)).trans
      (and_congr (hφ hF hS hA m hm hM f hf η hη) (hψ hF hS hA m hm hM f hf η hη))
  | .disj φ ψ =>
    obtain ⟨a, N, ha, hN, hkN, hφ⟩ := formula_l φ ξ hk hξ
    obtain ⟨b, M, hb, hM, _, hψ⟩ := formula_l ψ ξ hk hξ
    obtain ⟨P, hP, hkP, hφ, hψ⟩ := common_l hℳ hω hN hM hkN hφ hψ
    obtain ⟨c, hc, h⟩ := PowerlessUniformEvaluationLogic.disjunction_l hℳ hω ht hT ha hb
    refine ⟨c, P, hc, hP, hkP, ?_⟩
    intro A S F hF hS hA m hm hM f hf η hη
    exact (h hF f ((hS f).mpr ⟨m, hm, hf⟩)).trans
      (or_congr (hφ hF hS hA m hm hM f hf η hη) (hψ hF hS hA m hm hM f hf η hη))
  | .imp φ ψ =>
    obtain ⟨a, N, ha, hN, hkN, hφ⟩ := formula_l φ ξ hk hξ
    obtain ⟨b, M, hb, hM, _, hψ⟩ := formula_l ψ ξ hk hξ
    obtain ⟨P, hP, hkP, hφ, hψ⟩ := common_l hℳ hω hN hM hkN hφ hψ
    obtain ⟨c, hc, h⟩ := PowerlessUniformEvaluationLogic.implication_l hℳ hω ht hT ha hb
    refine ⟨c, P, hc, hP, hkP, ?_⟩
    intro A S F hF hS hA m hm hM f hf η hη
    exact (h hF f ((hS f).mpr ⟨m, hm, hf⟩)).trans
      (imp_congr (hφ hF hS hA m hm hM f hf η hη) (hψ hF hS hA m hm hM f hf η hη))
  | .iff φ ψ =>
    obtain ⟨a, N, ha, hN, hkN, hφ⟩ := formula_l φ ξ hk hξ
    obtain ⟨b, M, hb, hM, _, hψ⟩ := formula_l ψ ξ hk hξ
    obtain ⟨P, hP, hkP, hφ, hψ⟩ := common_l hℳ hω hN hM hkN hφ hψ
    obtain ⟨c, hc, h⟩ := PowerlessUniformEvaluationLogic.biconditional_l hℳ hω ht hT ha hb
    refine ⟨c, P, hc, hP, hkP, ?_⟩
    intro A S F hF hS hA m hm hM f hf η hη
    exact (h hF f ((hS f).mpr ⟨m, hm, hf⟩)).trans
      (iff_congr (hφ hF hS hA m hm hM f hf η hη) (hψ hF hS hA m hm hM f hf η hη))
  | .existsE .set φ =>
    obtain ⟨l, hl⟩ := PowerlessNatural.successor_exists_l hℳ k
    obtain ⟨b, N, hb, hN, hlN, hφ⟩ := formula_l φ (ξ.pushBound k)
      (PowerlessNatural.successor_mem_l hℳ hω hk hl) (PowerlessSourceEnvironment.push_l hξ hl)
    obtain ⟨c, hc, h⟩ := PowerlessUniformSourceSpecification.existential_l hℳ hω ht hT hk
      (PowerlessSourceEnvironment.fresh_l hℳ hξ) hb (hlN k ((hl k).mpr (Or.inr rfl))) hφ
    exact ⟨c, N, hc, hN, fun x hx => hlN x ((hl x).mpr (Or.inl hx)), h⟩
  | .forallE .set φ =>
    obtain ⟨l, hl⟩ := PowerlessNatural.successor_exists_l hℳ k
    obtain ⟨b, N, hb, hN, hlN, hφ⟩ := formula_l φ (ξ.pushBound k)
      (PowerlessNatural.successor_mem_l hℳ hω hk hl) (PowerlessSourceEnvironment.push_l hξ hl)
    obtain ⟨c, hc, h⟩ := PowerlessUniformSourceSpecification.universal_l hℳ hω ht hT hk
      (PowerlessSourceEnvironment.fresh_l hℳ hξ) hb (hlN k ((hl k).mpr (Or.inr rfl))) hφ
    exact ⟨c, N, hc, hN, fun x hx => hlN x ((hl x).mpr (Or.inl hx)), h⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessUniformSourceCompilation
