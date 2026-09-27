import BMSConstructibleBridge.PowerlessPartialTruthProgress
import BMSConstructibleBridge.PowerlessPartialTruthSuccessor

/-!
# 一般后继层部分真值的双向正确性

前驱匹配极性的正确性作为外部递推假设；严格子码的内部归纳
处理全部分类规则。小层只需真实有限支持，不要求完整核心。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessPartialTruthStep

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

variable {M N : type_l U} (hM : member_l ℳ M.val ω.val)
  (hN : PowerlessNatural.successor_l M.val N.val)
  (B : Formula ℒ [] PowerlessTruthOracle.context_m)
  (hB : ∀ p c f : type_l U,
    PowerlessLevyCertificate.class_l ω.val e.val T.val t₁.val t₂.val t₃.val c.val M.val p.val →
    (∃ k, member_l ℳ k ω.val ∧ map_l f.val k U) →
    (B.satisfies (PowerlessTruthOracle.env_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ M p c f) ↔
      PowerlessTruthSign.sign_l e.val t₁.val H p.val c.val f.val))

include hM hN hB

omit h𝒩 h₀ hR in
theorem quantifier_l
    (h₁ : Theory.Models (structure_l U hU₀)
      (PowerlessOracleIntroduction.theory_m (PowerlessPartialTruthIntroduction.oracle_m B)))
    {n p c : type_l U} {D : carrier_l ℳ}
    (hD : PowerlessLevyCertificate.certificate_l ω.val e.val T.val t₁.val t₂.val t₃.val D)
    (hn : subset_l n.val N.val)
    (hc : PowerlessLevyRule.quantifier_l ω.val e.val T.val t₁.val t₃.val D c.val n.val p.val)
    (hI : ∀ b : type_l U, member_l ℳ b.val c.val →
      PowerlessPartialTruthProperty.property_l (hU₀ := hU₀)
        (lift_m B) ω e T t₁ t₂ t₃ N D H b)
    (f : type_l U) (hs : PowerlessTruthSign.sign_l e.val t₁.val H p.val c.val f.val) :
    (lift_m B).satisfies
      (PowerlessTruthOracle.env_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ N p c f) := by
  obtain ⟨hp, _, i, b, m, q, hb, hm, hC⟩ := hc
  have hp₀ : p = e := Subtype.ext hp
  subst p
  have hQ := (PowerlessTruthSign.positive_l (PowerlessEvaluationTags.distinct_l hℳ ht).1).mp hs
  obtain ⟨_, k, hk, hf, hi, a, ha, g, hg, hfg, hgb⟩ :=
    (PowerlessEvaluationEquations.exists_l hℳ hω ht hT hH hC f.val).mp hQ
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  have hb₀ := (PowerlessFormulaConstructor.bounds_l hℳ hω ht.1 hT hC).2
  let i₀ : type_l U := ⟨i, hUT ω.val i ω.property hC.1⟩
  let b₀ : type_l U := ⟨b, hUT c.val b c.property hb₀⟩
  let m₀ : type_l U := ⟨m, hUT ω.val m ω.property (PowerlessLevyEntry.natural_l hb).2.1⟩
  let a₀ : type_l U := ⟨a, ha⟩
  let g₀ : type_l U := ⟨g, PowerlessStageFiniteGraphs.finite_l hℳ hω ht hT hU hδ
    (fun x hx => PowerlessOrdinal.transitive_l hδ.1 ω.val x hωδ hx) k hk g hg⟩
  have hJ := fun a ha F hF =>
    PowerlessStageAdditionIteration.limit_l hℳ hω ht hT hU hωδ hδ (a := a) (F := F) ha hF
  have hC₀ := (PowerlessFormulaCodeAbsolute.constructor_l (hB := hU₀)
    (t := t₃) (a := i₀) (b := b₀) (n := c) hℳ hUT hω ht.1 hT hJ).mpr hC
  have hi₀ := (PowerlessStageAmbientAssignments.slot_l (hU₀ := hU₀)
    (f := f) (i := i₀) hℳ hω ht hT hU hδ).mpr ⟨k, hk, hf, hi⟩
  have hg₀ := (PowerlessStageAmbientAssignments.finite_l (hU₀ := hU₀)
    (f := g₀) hℳ hω ht hT hU hδ).mpr ⟨k, hk, hg⟩
  have hfg₀ : PowerlessAssignmentUpdate.update_l (ℳ := structure_l U hU₀) f i₀ a₀ g₀ :=
    (PowerlessValueAbsolute.update_l hUT).mpr hfg
  have hA : (lift_m B).satisfies
      (PowerlessTruthOracle.env_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ N e b₀ g₀) := by
    rcases hm with ⟨hq, hm⟩ | ⟨_, hm⟩
    · have hb₁ : PowerlessLevyEntry.entry_l ω.val e.val T.val D b m e.val := by
        simpa only [hq] using hb
      exact hI b₀ hb₀ m₀ e (fun x hx => hn x (hm x hx)) hb₁ g₀ ⟨k, hk, hg⟩ (Or.inl ⟨rfl, hgb⟩)
    · exact PowerlessPartialTruthSuccessor.promotion_l hℳ hω ht hT hU hδ hωδ
        B hB h₁ hM hN e b₀ g₀ (hn m hm) ⟨D, hD, hb⟩ ⟨k, hk, hg⟩ (Or.inl ⟨rfl, hgb⟩)
  exact PowerlessPartialTruthIntroduction.exists_l B h₁ ω e T t₁ t₂ t₃ N c f i₀ b₀ a₀ g₀
    (PowerlessFormulaConstructor.natural_l hℳ hω ht.1 hT hC) hC₀ hi₀ hg₀ hfg₀ hA


theorem complete_l
    (h₁ : Theory.Models (structure_l U hU₀)
      (PowerlessOracleIntroduction.theory_m (PowerlessPartialTruthIntroduction.oracle_m B)))
    {D : carrier_l ℳ}
    (hD : PowerlessLevyCertificate.certificate_l ω.val e.val T.val t₁.val t₂.val t₃.val D) :
    ∀ c : type_l U, member_l ℳ c.val ω.val →
      PowerlessPartialTruthProperty.property_l (hU₀ := hU₀) (lift_m B) ω e T t₁ t₂ t₃ N D H c := by
  apply PowerlessPartialTruthProperty.induction_l hℳ (lift_m B) ω e T t₁ t₂ t₃ N D H hω
    (PowerlessStageStructure.transitive_l hℳ hω ht hT hU)
  intro c _ hI n p hn hc f hf hs
  rcases (hD.2 c.val n.val p.val hc).2 with hC | hC | hC | hC | ⟨m, q, hm, hC⟩
  · exact PowerlessPartialTruthIntroduction.bounded_l B hℳ hω ht hT hU hδ hωδ
      h𝒩 h₀ h₁ hR hH p c f hC hf hs
  · exact PowerlessPartialTruthProgress.boolean_l hℳ hω ht hT hU hδ hωδ hR hH
      B h₁ hn hC hI f hf hs
  · exact PowerlessPartialTruthProgress.bounded_l hℳ hω ht hT hU hδ hωδ hR hH
      B h₁ hn hC hI f hf hs
  · exact quantifier_l hℳ hω ht hT hU hδ hωδ hH hM hN B hB h₁ hD hn hC hI f hs
  · exact PowerlessPartialTruthSuccessor.promotion_l hℳ hω ht hT hU hδ hωδ
      B hB h₁ hM hN p c f (hn m hm) ⟨D, hD, hC⟩ hf hs


/-- 一般后继层的匹配极性双向正确性，由真实内部代码归纳消去推进条件。 -/
theorem source_l
    (h₁ : Theory.Models (structure_l U hU₀)
      (PowerlessOracleIntroduction.theory_m (PowerlessPartialTruthIntroduction.oracle_m B)))
    (p c f : type_l U)
    (hc : PowerlessLevyCertificate.class_l ω.val e.val T.val t₁.val t₂.val t₃.val c.val N.val p.val)
    (hf : ∃ k, member_l ℳ k ω.val ∧ map_l f.val k U) :
    (lift_m B).satisfies
      (PowerlessTruthOracle.env_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ N p c f) ↔
        PowerlessTruthSign.sign_l e.val t₁.val H p.val c.val f.val := by
  constructor
  · exact PowerlessPartialTruthSuccessor.source_l hℳ hω ht hT hU hδ hωδ B hB h𝒩 hR hH hN p c f
  · intro hs
    obtain ⟨D, hD, hc⟩ := hc
    exact complete_l hℳ hω ht hT hU hδ hωδ h𝒩 h₀ hR hH hM hN B hB h₁
      hD c (PowerlessLevyEntry.natural_l hc).1 N p (fun _ hx => hx) hc f hf hs


end YesMetaZFC.BMS.ConstructibleBridge.PowerlessPartialTruthStep
