import BMSConstructibleBridge.PowerlessSourceBounded
import BMSConstructibleBridge.PowerlessSourceSpecification
import BMSConstructibleBridge.PowerlessBoundedCode

/-!
# 原源有界存在量词与指定复合数码的编译对应

界项在外层上下文，故其槽不同于新绑定槽。结果保留实际复合编码关系，
使后续有界分类证书可读取同一个数码，不从两次编译存在性猜测数码相同。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceBoundedCompilation

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure PowerlessSourceSpecification StabilityFrame

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ S F b k N : carrier_l ℳ} {hA : ∃ a, member_l ℳ a A}
    (hω : omega_l ω) (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F)
    (hS : ∀ f, member_l ℳ f S ↔ ∃ m, member_l ℳ m ω ∧ map_l f m A)
    {ξ : Env ℳ Γ Δ} {φ : Formula ℒ (.set :: Γ) Δ} (s : Term ℒ Γ Δ .set)
    (hk : member_l ℳ k ω) (hξ : ∀ t : Term ℒ Γ Δ .set, t.eval ξ ≠ k)
    (hs : member_l ℳ (s.eval ξ) ω) (hb : member_l ℳ b ω) (hN : member_l ℳ k N)
    (h : spec_l ω A F b N hA (ξ.pushBound k) φ) : ∃ c, member_l ℳ c ω ∧
      PowerlessBoundedCode.code_l ω e T t₂ t₃ k (s.eval ξ) b c ∧
      spec_l ω A F c N hA ξ (membershipLevyBound.boundedExists s φ) := by
  obtain ⟨c, hc, hC⟩ := PowerlessBoundedCode.exists_l hℳ hω ht hT hk hs hb (hξ s).symm
  refine ⟨c, hc, hC, ?_⟩
  intro m hm hM f hf η hη
  refine (PowerlessBoundedCode.equation_l hℳ hω ht hT hF hS hC f ((hS f).mpr ⟨m, hm, hf⟩)).trans ?_
  rw [Formula.LevyBound.satisfies_boundedExists membershipLevyBound η s φ]
  change PowerlessBoundedQuantifier.exists_l ω A F f k (s.eval ξ) b ↔
    ∃ a : type_l A, member_l ℳ a.val (s.eval η).val ∧ Formula.satisfies (η.pushBound a) φ
  constructor
  · rintro ⟨n, _, hf₀, _, z, hz, a, ha, g, hg, h₀, h₁⟩
    have h₂ := PowerlessAssignmentUpdate.length_unique_l hℳ hf₀ hf
    subst n
    have hz₀ := PowerlessFunction.value_unique_l hℳ hf hz (hη s)
    have ha₀ := (PowerlessFunction.value_mem_l hℳ hg (PowerlessAssignmentUpdate.at_l h₀)).2
    exact ⟨⟨a, ha₀⟩, hz₀ ▸ ha, (h m hm hM g hg (η.pushBound ⟨a, ha₀⟩)
      (PowerlessSourceEnvironment.update_l hξ hη ⟨a, ha₀⟩ h₀)).mp h₁⟩
  · rintro ⟨a, ha, h₀⟩
    obtain ⟨g, hg, h₁⟩ := PowerlessAssignmentUpdate.exists_l hℳ hf (hM k hN) a.property
    exact ⟨m, hm, hf, hM k hN, (s.eval η).val, hη s, a.val, ha, g, hg, h₁,
      (h m hm hM g hg (η.pushBound a) (PowerlessSourceEnvironment.update_l hξ hη a h₁)).mpr h₀⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceBoundedCompilation
