import BMSConstructibleBridge.PowerlessPartialTruthIntroduction
import BMSConstructibleBridge.PowerlessPartialTruthProperty

/-!
# 部分真值完备性的实际构造子推进

与非分支按真实分类记录读取两个严格较小子码，将完整求值的真假
方程送入小层的有限支持引入规则。不假定当前代码的接受完备性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessPartialTruthProgress

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
  (hR : PowerlessEvaluationOperator.assignments_l ω.val U R)
  (hH : PowerlessEvaluationRecursion.evaluation_l ω.val e.val T.val U t₁.val t₂.val t₃.val R H)

include hℳ hω ht hT hU hδ hωδ hR hH

theorem boolean_l (B : Formula ℒ [] PowerlessTruthOracle.context_m)
    (h₁ : Theory.Models (structure_l U hU₀)
      (PowerlessOracleIntroduction.theory_m (PowerlessPartialTruthIntroduction.oracle_m B)))
    {N n p c : type_l U} {D : carrier_l ℳ} (hn : subset_l n.val N.val)
    (hc : PowerlessLevyRule.boolean_l ω.val e.val T.val t₁.val t₂.val D c.val n.val p.val)
    (hI : ∀ b : type_l U, member_l ℳ b.val c.val →
      PowerlessPartialTruthProperty.property_l (hU₀ := hU₀)
        (lift_m B) ω e T t₁ t₂ t₃ N D H b)
    (f : type_l U) (hf : ∃ k, member_l ℳ k ω.val ∧ map_l f.val k U)
    (hs : PowerlessTruthSign.sign_l e.val t₁.val H p.val c.val f.val) :
    (lift_m B).satisfies
      (PowerlessTruthOracle.env_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ N p c f) := by
  obtain ⟨a, b, k, l, q, hp, hk, hl, ha, hb, hC⟩ := hc
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  obtain ⟨ha₀, hb₀⟩ := PowerlessFormulaConstructor.bounds_l hℳ hω ht.1 hT hC
  let a₀ : type_l U := ⟨a, hUT c.val a c.property ha₀⟩
  let b₀ : type_l U := ⟨b, hUT c.val b c.property hb₀⟩
  let k₀ : type_l U := ⟨k, hUT ω.val k ω.property (PowerlessLevyEntry.natural_l ha).2.1⟩
  let l₀ : type_l U := ⟨l, hUT ω.val l ω.property (PowerlessLevyEntry.natural_l hb).2.1⟩
  let q₀ : type_l U := ⟨q, hUT ω.val q ω.property (PowerlessLevyEntry.natural_l ha).2.2⟩
  have hA := hI a₀ ha₀ k₀ q₀ (fun x hx => hn x (hk x hx)) ha f hf
  have hB := hI b₀ hb₀ l₀ q₀ (fun x hx => hn x (hl x hx)) hb f hf
  have hJ := fun a ha F hF =>
    PowerlessStageAdditionIteration.limit_l hℳ hω ht hT hU hωδ hδ (a := a) (F := F) ha hF
  have hC₀ := (PowerlessFormulaCodeAbsolute.constructor_l (hB := hU₀)
    (t := t₂) (a := a₀) (b := b₀) (n := c) hℳ hUT hω ht.1 hT hJ).mpr hC
  have hf₀ := (PowerlessStageAmbientAssignments.finite_l (hU₀ := hU₀) hℳ hω ht hT hU hδ).mpr hf
  have hc₀ := PowerlessFormulaConstructor.natural_l hℳ hω ht.1 hT hC
  have hF := (hR f.val).mpr hf
  have hE := PowerlessEvaluationEquations.nand_l hℳ hω ht hT hH hC f.val
  simp only [hF, true_and] at hE
  have he₁ := (PowerlessEvaluationTags.distinct_l hℳ ht).1
  have hS := (PowerlessTruthSign.nand_l he₁ hE).mp hs
  apply PowerlessPartialTruthIntroduction.nand_l B h₁ ω e T t₁ t₂ t₃ N p c f a₀ b₀ hc₀ hC₀ hf₀
  rcases hp with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · have hq₀ : q₀ = t₁ := Subtype.ext hq
    rw [hq₀] at hA hB
    rcases hS with ⟨_, h | h⟩ | ⟨h, _, _⟩
    · exact Or.inl ⟨Subtype.ext hp, Or.inl (hA h)⟩
    · exact Or.inl ⟨Subtype.ext hp, Or.inr (hB h)⟩
    · exact (he₁ (hp.symm.trans h)).elim
  · have hq₀ : q₀ = e := Subtype.ext hq
    rw [hq₀] at hA hB
    rcases hS with ⟨h, _⟩ | ⟨_, h, h'⟩
    · exact (he₁ (h.symm.trans hp)).elim
    · exact Or.inr ⟨Subtype.ext hp, hA h, hB h'⟩


/-- 第一层内的正无界存在：同极性使用子码归纳，反极性使用严格降层。 -/
theorem quantifier_l (B : Formula ℒ [] PowerlessTruthOracle.context_m)
    (h𝒩 : Theory.Models (structure_l U hU₀) PowerlessFiniteStageEvaluation.theory_m)
    (h₀ : Theory.Models (structure_l U hU₀) PowerlessTruthIntroduction.theory_m)
    (h₁ : Theory.Models (structure_l U hU₀)
      (PowerlessOracleIntroduction.theory_m (PowerlessPartialTruthIntroduction.oracle_m B)))
    {N n p c : type_l U} {D : carrier_l ℳ}
    (hD : PowerlessLevyCertificate.certificate_l ω.val e.val T.val t₁.val t₂.val t₃.val D)
    (hN : subset_l N.val t₁.val) (hn : subset_l n.val N.val)
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
  have hB : (lift_m B).satisfies
      (PowerlessTruthOracle.env_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ N e b₀ g₀) := by
    rcases hm with ⟨hq, hm⟩ | ⟨_, hm⟩
    · have hb₁ : PowerlessLevyEntry.entry_l ω.val e.val T.val D b m e.val := by
        simpa only [hq] using hb
      exact hI b₀ hb₀ m₀ e (fun x hx => hn x (hm x hx)) hb₁ g₀ ⟨k, hk, hg⟩ (Or.inl ⟨rfl, hgb⟩)
    · exact PowerlessPartialTruthIntroduction.promotion_l B hℳ hω ht hT hU hδ hωδ
        h𝒩 h₀ h₁ hR hH e b₀ g₀ hN (hn m hm) ⟨D, hD, hb⟩ ⟨k, hk, hg⟩ (Or.inl ⟨rfl, hgb⟩)
  exact PowerlessPartialTruthIntroduction.exists_l B h₁ ω e T t₁ t₂ t₃ N c f i₀ b₀ a₀ g₀
    (PowerlessFormulaConstructor.natural_l hℳ hω ht.1 hT hC) hC₀ hi₀ hg₀ hfg₀ hB

/-- 有界两极性都沿实际严格子码推进；负分支不要求界集合有限。 -/
theorem bounded_l (B : Formula ℒ [] PowerlessTruthOracle.context_m)
    (h₁ : Theory.Models (structure_l U hU₀)
      (PowerlessOracleIntroduction.theory_m (PowerlessPartialTruthIntroduction.oracle_m B)))
    {N n p c : type_l U} {D : carrier_l ℳ} (hn : subset_l n.val N.val)
    (hc : PowerlessLevyRule.bounded_l ω.val e.val T.val t₂.val t₃.val D c.val n.val p.val)
    (hI : ∀ b : type_l U, member_l ℳ b.val c.val →
      PowerlessPartialTruthProperty.property_l (hU₀ := hU₀)
        (lift_m B) ω e T t₁ t₂ t₃ N D H b)
    (f : type_l U) (hf : ∃ k, member_l ℳ k ω.val ∧ map_l f.val k U)
    (hs : PowerlessTruthSign.sign_l e.val t₁.val H p.val c.val f.val) :
    (lift_m B).satisfies
      (PowerlessTruthOracle.env_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ N p c f) := by
  classical
  obtain ⟨i, j, b, m, hm, hb, hC⟩ := hc
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  obtain ⟨hi, hj, hb₀⟩ := PowerlessBoundedCode.bounds_l hℳ hω ht.1 hT hC
  let i₀ : type_l U := ⟨i, hUT c.val i c.property hi⟩
  let j₀ : type_l U := ⟨j, hUT c.val j c.property hj⟩
  let b₀ : type_l U := ⟨b, hUT c.val b c.property hb₀⟩
  let m₀ : type_l U := ⟨m, hUT ω.val m ω.property (PowerlessLevyEntry.natural_l hb).2.1⟩
  have hA := hI b₀ hb₀ m₀ p (fun x hx => hn x (hm x hx)) hb
  have hJ := fun a ha F hF =>
    PowerlessStageAdditionIteration.limit_l hℳ hω ht hT hU hωδ hδ (a := a) (F := F) ha hF
  have hC₀ := (PowerlessBoundedCodeAbsolute.code_l (hB := hU₀)
    (t₂ := t₂) (t₃ := t₃) (i := i₀) (j := j₀) (b := b₀) (c := c)
    hℳ hUT hω ht.1 hT hJ).mpr hC
  have hc₀ : member_l ℳ c.val ω.val := by
    obtain ⟨_, _, _, _, _, _, _, h⟩ := hC
    exact PowerlessFormulaConstructor.natural_l hℳ hω ht.1 hT h
  have hf₀ := (PowerlessStageAmbientAssignments.finite_l (hU₀ := hU₀)
    (f := f) hℳ hω ht hT hU hδ).mpr hf
  have hG (k : carrier_l ℳ) (hk : member_l ℳ k ω.val) (g : carrier_l ℳ) (hg : map_l g k U) :
      member_l ℳ g U :=
    PowerlessStageFiniteGraphs.finite_l hℳ hω ht hT hU hδ
      (fun x hx => PowerlessOrdinal.transitive_l hδ.1 ω.val x hωδ hx) k hk g hg
  have hE := PowerlessBoundedCode.equation_l hℳ hω ht hT hH hR hC f.val ((hR f.val).mpr hf)
  rcases hs with ⟨hp, hQ⟩ | ⟨hp, hQ⟩
  · have hp₀ : p = e := Subtype.ext hp
    subst p
    obtain ⟨k, hk, hf, hi, z, hz, a, ha, g, hg, hfg, hgb⟩ := hE.mp hQ
    have hzU := (PowerlessValueAbsolute.coordinates_l hUT f.property hz).2
    let z₀ : type_l U := ⟨z, hzU⟩
    let a₀ : type_l U := ⟨a, hUT z a hzU ha⟩
    let g₀ : type_l U := ⟨g, hG k hk g hg⟩
    have hi₀ := (PowerlessStageAmbientAssignments.slot_l (hU₀ := hU₀)
      (f := f) (i := i₀) hℳ hω ht hT hU hδ).mpr ⟨k, hk, hf, hi⟩
    have hg₀ := (PowerlessStageAmbientAssignments.finite_l (hU₀ := hU₀)
      (f := g₀) hℳ hω ht hT hU hδ).mpr ⟨k, hk, hg⟩
    have hz₀ : value_l (ℳ := structure_l U hU₀) f j₀ z₀ :=
      (PowerlessSourceGraphAbsolute.value_l hUT).mpr hz
    have hfg₀ : PowerlessAssignmentUpdate.update_l (ℳ := structure_l U hU₀) f i₀ a₀ g₀ :=
      (PowerlessValueAbsolute.update_l hUT).mpr hfg
    exact PowerlessPartialTruthIntroduction.positive_l B h₁ ω e T t₁ t₂ t₃ N c f i₀ j₀ b₀ z₀ a₀ g₀
      hc₀ hC₀ hi₀ hz₀ ha hg₀ hfg₀ (hA g₀ ⟨k, hk, hg⟩ (Or.inl ⟨rfl, hgb⟩))
  · have hp₀ : p = t₁ := Subtype.ext hp
    subst p
    apply PowerlessPartialTruthIntroduction.negative_l B h₁ ω e T t₁ t₂ t₃ N c f i₀ j₀ b₀ hc₀ hC₀ hf₀
    by_cases hi₀ : PowerlessAmbientAssignments.slot_l (ℳ := structure_l U hU₀) ω f i₀
    · right
      intro z hz a ha
      obtain ⟨k, hk, hf, hi⟩ := (PowerlessStageAmbientAssignments.slot_l hℳ hω ht hT hU hδ).mp hi₀
      obtain ⟨g, hg, hfg⟩ := PowerlessAssignmentUpdate.exists_l hℳ hf hi a.property
      let g₀ : type_l U := ⟨g, hG k hk g hg⟩
      have hg₀ := (PowerlessStageAmbientAssignments.finite_l (hU₀ := hU₀)
        (f := g₀) hℳ hω ht hT hU hδ).mpr ⟨k, hk, hg⟩
      have hz₀ := (PowerlessSourceGraphAbsolute.value_l hUT).mp hz
      have hfg₀ : PowerlessAssignmentUpdate.update_l (ℳ := structure_l U hU₀) f i₀ a g₀ :=
        (PowerlessValueAbsolute.update_l hUT).mpr hfg
      refine ⟨g₀, hg₀, hfg₀, hA g₀ ⟨k, hk, hg⟩ (Or.inr ⟨rfl, ?_⟩)⟩
      intro hgb
      exact hQ (hE.mpr ⟨k, hk, hf, hi, z.val, hz₀, a.val, ha, g, hg, hfg, hgb⟩)
    · exact Or.inl hi₀
end YesMetaZFC.BMS.ConstructibleBridge.PowerlessPartialTruthProgress
