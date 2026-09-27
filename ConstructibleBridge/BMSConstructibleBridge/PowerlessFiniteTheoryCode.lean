import BMSConstructibleBridge.PowerlessUniformSourceCompilation
import BMSConstructibleBridge.PowerlessExtension

/-!
# 用跨域通用的一个数码表示原有限理论

有限闭句合取的数码 c 与赋值长度 N 在所有域之前选取。
任意非空实际域满足原有限理论，当且仅当存在长度 N 的实际赋值使求值器接受 c。
闭句仍需足够长的赋值，不以空赋值冒充其编译规格。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteTheoryCode

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

universe u

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T) (Γ : List (Sentence ℒ)) :
    ∃ c N, member_l ℳ c ω ∧ member_l ℳ N ω ∧
      ∀ {A S F}, ∀ hA : ∃ a, member_l ℳ a A,
        PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F →
        (∀ f, member_l ℳ f S ↔ ∃ m, member_l ℳ m ω ∧ map_l f m A) →
        (Theory.Models (structure_l A hA) (Theory.ofList Γ) ↔
          ∃ f, map_l f N A ∧ PowerlessEvaluationClause.query_l F c f) := by
  have hξ : PowerlessSourceEnvironment.bounded_l (ℳ := ℳ) Env.empty e := by
    intro t
    match t with
    | .bvar v => nomatch v
    | .fvar v => nomatch v
    | .app f _ => nomatch f
  obtain ⟨c, N, hc, hN, _, hC⟩ := PowerlessUniformSourceCompilation.formula_l hℳ hω ht hT
    (Formula.conjunctionList Γ) Env.empty (PowerlessNatural.zero_mem_l hℳ hω ht.1) hξ
  refine ⟨c, N, hc, hN, ?_⟩
  intro A S F hA hF hS
  have h (f : carrier_l ℳ) (hf : map_l f N A) :
      PowerlessEvaluationClause.query_l F c f ↔ Theory.Models (structure_l A hA) (Theory.ofList Γ) :=
    (hC hF hS hA N hN (fun _ h => h) f hf Env.empty (PowerlessSourceEnvironment.empty_l f)).trans
      (Formula.satisfies_conjunctionList_iff Env.empty Γ)
  constructor
  · intro hΓ
    obtain ⟨a, ha⟩ := hA
    obtain ⟨f, B, hf, hV⟩ := PowerlessExtension.constant_l hℳ N a
    have hfA : map_l f N A := PowerlessFunction.range_l hℳ hf (fun i b hb => by
      have hba := ((hV i b).mp hb).2
      exact hba.symm ▸ ha)
    exact ⟨f, hfA, (h f hfA).mpr hΓ⟩
  · rintro ⟨f, hf, hF⟩
    exact (h f hf).mp hF

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteTheoryCode
