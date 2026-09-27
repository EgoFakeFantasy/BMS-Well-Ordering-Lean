import BMSConstructibleBridge.PowerlessPartialTruthFinite
import BMSConstructibleBridge.PowerlessTruthStage

/-!
# 任意外部有限部分真值族的实际层

有限列表收集原低层矩阵所需支持；同一实际真极限层中，
全部指定有限层号的数码及匹配极性双向正确性同时成立。
环境仍使用完整 PowerlessTheory，不是 Z₂ 推导传输。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthFiniteStage

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

def formulas_m (k : Nat) : List (Formula ℒ [] PowerlessTruthOracle.context_m) :=
  (List.range k).map (fun j => PowerlessPartialTruthIntroduction.oracle_m (PowerlessPartialTruth.formula_m j))

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (k : Nat) (α : carrier_l ℳ) (hα : PowerlessOrdinal.ordinal_l α) :
    ∃ δ U R H, ∃ hU₀ : ∃ x, member_l ℳ x U,
    ∃ w z V s₁ s₂ s₃ : type_l U,
      PowerlessStagePair.limit_l δ ∧ member_l ℳ α δ ∧ member_l ℳ ω δ ∧
      PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ δ U ∧
      w.val = ω ∧ z.val = e ∧ V.val = T ∧ s₁.val = t₁ ∧ s₂.val = t₂ ∧ s₃.val = t₃ ∧
      PowerlessEvaluationOperator.assignments_l ω U R ∧
      PowerlessEvaluationRecursion.evaluation_l ω e T U t₁ t₂ t₃ R H ∧
      Theory.Models (structure_l U hU₀) (Theory.ofList (PowerlessTruthStage.basis_m (formulas_m k))) ∧
      ∀ j, j ≤ k → ∃ n : type_l U, PowerlessNumeral.numeral_l e j n.val ∧
        ∀ p c f : type_l U,
          PowerlessLevyCertificate.class_l ω e T t₁ t₂ t₃ c.val n.val p.val →
          (∃ a, member_l ℳ a ω ∧ map_l f.val a U) →
          ((PowerlessPartialTruth.formula_m j).satisfies
            (PowerlessTruthOracle.env_l (ℳ := structure_l U hU₀) w z V s₁ s₂ s₃ n p c f) ↔
              PowerlessTruthSign.sign_l e t₁ H p.val c.val f.val) := by
  obtain ⟨δ, U, R, H, hU₀, w, z, V, s₁, s₂, s₃,
    hδ, hαδ, hωδ, hU, hw, hz, hV, hs₁, hs₂, hs₃, hR, hH, h𝒩, _, _, _⟩ :=
    PowerlessTruthStage.exists_l hℳ hω ht hT (formulas_m k) α hα
  subst ω
  subst e
  subst T
  subst t₁
  subst t₂
  subst t₃
  have h₀ : Theory.Models (structure_l U hU₀) PowerlessFiniteStageEvaluation.theory_m :=
    fun φ hφ => h𝒩 φ (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hφ))))
  have h₁ : Theory.Models (structure_l U hU₀) PowerlessTruthIntroduction.theory_m :=
    fun φ hφ => h𝒩 φ (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hφ))))
  have hS : ∀ a, a < k → Theory.Models (structure_l U hU₀)
      (PowerlessOracleIntroduction.theory_m
        (PowerlessPartialTruthIntroduction.oracle_m (PowerlessPartialTruth.formula_m a))) := by
    intro a ha φ hφ
    apply h𝒩 φ
    exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
      ⟨_, List.mem_map.mpr ⟨a, List.mem_range.mpr ha, rfl⟩, List.mem_append.mpr (Or.inr hφ)⟩))
  refine ⟨δ, U, R, H, hU₀, w, z, V, s₁, s₂, s₃,
    hδ, hαδ, hωδ, hU, rfl, rfl, rfl, rfl, rfl, rfl, hR, hH, h𝒩, ?_⟩
  intro j hj
  obtain ⟨a, ha⟩ := PowerlessNumeral.exists_l hℳ z.val j
  have haω := PowerlessNumeral.natural_l hℳ hω ht.1 ha
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  let n : type_l U := ⟨a, hUT w.val a w.property haω⟩
  refine ⟨n, ha, ?_⟩
  intro p c f hc hf
  exact PowerlessPartialTruthFinite.source_l hℳ hω ht hT hU hδ hωδ h₀ h₁ hR hH
    j (fun a ha => hS a (Nat.lt_of_lt_of_le ha hj)) n ha p c f hc hf

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthFiniteStage

