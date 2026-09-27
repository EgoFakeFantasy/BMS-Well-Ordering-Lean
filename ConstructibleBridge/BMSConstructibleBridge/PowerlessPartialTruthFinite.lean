import BMSConstructibleBridge.PowerlessPartialTruthStep
import BMSConstructibleBridge.PowerlessNumeral

/-!
# 外部固定有限层部分真值的正确性

实际内部数码按外部 Nat 递推。每一步消费原有限支持与已证明后继定理，
不假定模型内部自然数标准，也不向小层加入完整核心。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessPartialTruthFinite

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure PowerlessPartialTruth

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U δ R H : carrier_l ℳ}
  {hU₀ : ∃ x, member_l ℳ x U} (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val)
  (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
  (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
  (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U)
  (hδ : PowerlessStagePair.limit_l δ) (hωδ : member_l ℳ ω.val δ)
  (h𝒩 : Theory.Models (structure_l U hU₀) PowerlessFiniteStageEvaluation.theory_m)
  (h₀ : Theory.Models (structure_l U hU₀) PowerlessTruthIntroduction.theory_m)
  (hR : PowerlessEvaluationOperator.assignments_l ω.val U R)
  (hH : PowerlessEvaluationRecursion.evaluation_l ω.val e.val T.val U t₁.val t₂.val t₃.val R H)

include hℳ hω ht hT hU hδ hωδ h𝒩 h₀ hR hH


theorem source_l (k : Nat)
    (hS : ∀ j, j < k → Theory.Models (structure_l U hU₀)
      (PowerlessOracleIntroduction.theory_m (PowerlessPartialTruthIntroduction.oracle_m (formula_m j))))
    (n : type_l U) (hn : PowerlessNumeral.numeral_l e.val k n.val)
    (p c f : type_l U)
    (hc : PowerlessLevyCertificate.class_l ω.val e.val T.val t₁.val t₂.val t₃.val c.val n.val p.val)
    (hf : ∃ j, member_l ℳ j ω.val ∧ map_l f.val j U) :
    (formula_m k).satisfies
      (PowerlessTruthOracle.env_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ n p c f) ↔
        PowerlessTruthSign.sign_l e.val t₁.val H p.val c.val f.val := by
  induction k generalizing n p c f with
  | zero =>
    have hn₀ : n = e := Subtype.ext hn
    subst n
    exact PowerlessPartialTruthZero.source_l hℳ hω ht hT hU hδ hωδ h𝒩 h₀ hR hH p c f
      (PowerlessLevyZero.class_l hℳ hω ht.1 hT hc) hf
  | succ k hI =>
    obtain ⟨a, ha, han⟩ := hn
    have haω := PowerlessNumeral.natural_l hℳ hω ht.1 ha
    have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
    let m : type_l U := ⟨a, hUT ω.val a ω.property haω⟩
    have hB : ∀ p c f : type_l U,
        PowerlessLevyCertificate.class_l ω.val e.val T.val t₁.val t₂.val t₃.val c.val m.val p.val →
        (∃ j, member_l ℳ j ω.val ∧ map_l f.val j U) →
        ((formula_m k).satisfies
          (PowerlessTruthOracle.env_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ m p c f) ↔
            PowerlessTruthSign.sign_l e.val t₁.val H p.val c.val f.val) := by
      intro p c f hc hf
      exact hI (fun j hj => hS j (Nat.lt_trans hj (Nat.lt_succ_self k))) m ha p c f hc hf
    exact PowerlessPartialTruthStep.source_l hℳ hω ht hT hU hδ hωδ h𝒩 h₀ hR hH
      haω han (formula_m k) hB (hS k (Nat.lt_succ_self k)) p c f hc hf

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessPartialTruthFinite

