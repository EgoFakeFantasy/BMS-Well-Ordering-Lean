import BMSConstructibleBridge.PowerlessPartialTruthIntroduction
import BMSConstructibleBridge.PowerlessLevyCertificateAbsolute

/-!
# 实际层中后继部分真值的低层调用

内部前驱唯一性连接指定前驱；分类与有限赋值按实际层的绝对性传输。
前驱匹配极性的双向正确性仍是递推假设，不在此宣称整族递推完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessPartialTruthSuccessor

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure PowerlessPartialTruth PowerlessTruthOracle

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U δ H : carrier_l ℳ}
  {hU₀ : ∃ x, member_l ℳ x U} (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ m n : type_l U} (hω : omega_l ω.val)
  (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
  (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
  (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U)
  (hδ : PowerlessStagePair.limit_l δ) (hωδ : member_l ℳ ω.val δ)
  (B : Formula ℒ [] context_m)
  (hB : ∀ p c f : type_l U,
    PowerlessLevyCertificate.class_l ω.val e.val T.val t₁.val t₂.val t₃.val c.val m.val p.val →
    (∃ k, member_l ℳ k ω.val ∧ map_l f.val k U) →
    (B.satisfies (env_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ m p c f) ↔
      PowerlessTruthSign.sign_l e.val t₁.val H p.val c.val f.val))

include hℳ hω ht hT hU hδ hωδ hB

theorem lower_sound_l (hn : PowerlessNatural.successor_l m.val n.val) (p c f : type_l U)
    (h : PowerlessPartialTruth.lower_l (ℳ := structure_l U hU₀) B ω e T t₁ t₂ t₃ n p c f) :
    PowerlessTruthSign.sign_l e.val t₁.val H p.val c.val f.val := by
  classical
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  obtain ⟨a, _, ha, hf, h⟩ := h
  have ha₀ : a = m := Subtype.ext (PowerlessNatural.successor_injective_l hℳ
    ((PowerlessSourceNaturalAbsolute.successor_l hUT).mp ha) hn)
  subst a
  have hf₀ := (PowerlessStageAmbientAssignments.finite_l hℳ hω ht hT hU hδ).mp hf
  have hI := fun a ha F hF =>
    PowerlessStageAdditionIteration.limit_l hℳ hω ht hT hU hωδ hδ (a := a) (F := F) ha hF
  have hD := PowerlessStageFiniteSubsets.finite_l hℳ hω ht hT hU hδ
    (fun a ha => PowerlessOrdinal.transitive_l hδ.1 ω.val a hωδ ha)
  have he₁ := (PowerlessEvaluationTags.distinct_l hℳ ht).1
  rcases h with ⟨hc, h⟩ | ⟨hc, h⟩
  · have hP := hB e c f
      ((PowerlessLevyCertificateAbsolute.class_l hℳ hUT hω ht.1 hT hI hD).mp hc) hf₀
    simp only [PowerlessTruthSign.sign_l, he₁, false_and, or_false, true_and, eq_self] at hP
    rw [hP] at h
    rcases h with ⟨hp, h⟩ | ⟨hp, h⟩
    · exact Or.inl ⟨congrArg Subtype.val hp, h⟩
    · exact Or.inr ⟨congrArg Subtype.val hp, h⟩
  · have hQ := hB t₁ c f
      ((PowerlessLevyCertificateAbsolute.class_l hℳ hUT hω ht.1 hT hI hD).mp hc) hf₀
    simp only [PowerlessTruthSign.sign_l, he₁.symm, false_and, false_or, true_and, eq_self] at hQ
    rw [hQ] at h
    rcases h with ⟨hp, h⟩ | ⟨hp, h⟩
    · exact Or.inr ⟨congrArg Subtype.val hp, h⟩
    · exact Or.inl ⟨congrArg Subtype.val hp, Classical.not_not.mp h⟩

/-- 指定前驱上的分类与真值，经实际层绝对性产生后继接受。 -/
theorem lower_complete_l
    (h₁ : Theory.Models (structure_l U hU₀)
      (PowerlessOracleIntroduction.theory_m (PowerlessPartialTruthIntroduction.oracle_m B)))
    (hm : member_l ℳ m.val ω.val) (hn : PowerlessNatural.successor_l m.val n.val)
    (p c f : type_l U)
    (hc : PowerlessLevyCertificate.class_l ω.val e.val T.val t₁.val t₂.val t₃.val c.val m.val e.val ∨
      PowerlessLevyCertificate.class_l ω.val e.val T.val t₁.val t₂.val t₃.val c.val m.val t₁.val)
    (hf : ∃ k, member_l ℳ k ω.val ∧ map_l f.val k U)
    (h : PowerlessTruthSign.sign_l e.val t₁.val H p.val c.val f.val) :
    (lift_m B).satisfies (env_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ n p c f) := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  have hI := fun a ha F hF =>
    PowerlessStageAdditionIteration.limit_l hℳ hω ht hT hU hωδ hδ (a := a) (F := F) ha hF
  have hD := PowerlessStageFiniteSubsets.finite_l hℳ hω ht hT hU hδ
    (fun a ha => PowerlessOrdinal.transitive_l hδ.1 ω.val a hωδ ha)
  have hcω : member_l ℳ c.val ω.val := by
    rcases hc with hc | hc
    · exact (PowerlessLevyCertificate.natural_l hc).1
    · exact (PowerlessLevyCertificate.natural_l hc).1
  have he₁ := (PowerlessEvaluationTags.distinct_l hℳ ht).1
  apply PowerlessPartialTruthIntroduction.successor_l B h₁ (m := m) (n := n) (p := p) (c := c) (f := f)
    (ω := ω) (e := e) (T := T) (t₁ := t₁) (t₂ := t₂) (t₃ := t₃) hm
    ((PowerlessSourceNaturalAbsolute.successor_l hUT).mpr hn) hcω
    ((PowerlessStageAmbientAssignments.finite_l hℳ hω ht hT hU hδ).mpr hf)
  · exact hc.imp
      (PowerlessLevyCertificateAbsolute.class_l hℳ hUT hω ht.1 hT hI hD).mpr
      (PowerlessLevyCertificateAbsolute.class_l hℳ hUT hω ht.1 hT hI hD).mpr
  · intro hc
    have hP := hB e c f
      ((PowerlessLevyCertificateAbsolute.class_l hℳ hUT hω ht.1 hT hI hD).mp hc) hf
    simpa only [PowerlessTruthSign.sign_l, he₁, false_and, or_false, true_and, eq_self] using hP
  · intro hc
    have hQ := hB t₁ c f
      ((PowerlessLevyCertificateAbsolute.class_l hℳ hUT hω ht.1 hT hI hD).mp hc) hf
    simpa only [PowerlessTruthSign.sign_l, he₁.symm, false_and, false_or, true_and, eq_self] using hQ
  · rcases h with ⟨hp, h⟩ | ⟨hp, h⟩
    · exact Or.inl ⟨Subtype.ext hp, h⟩
    · exact Or.inr ⟨Subtype.ext hp, h⟩


/-- 任意严格低层分类先提升到指定前驱，再进入当前后继接受。 -/
theorem promotion_l
    (h₁ : Theory.Models (structure_l U hU₀)
      (PowerlessOracleIntroduction.theory_m (PowerlessPartialTruthIntroduction.oracle_m B)))
    (hm : member_l ℳ m.val ω.val) (hn : PowerlessNatural.successor_l m.val n.val)
    (p c f : type_l U) {a q : carrier_l ℳ} (ha : member_l ℳ a n.val)
    (hc : PowerlessLevyCertificate.class_l ω.val e.val T.val t₁.val t₂.val t₃.val c.val a q)
    (hf : ∃ k, member_l ℳ k ω.val ∧ map_l f.val k U)
    (h : PowerlessTruthSign.sign_l e.val t₁.val H p.val c.val f.val) :
    (lift_m B).satisfies (env_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ n p c f) := by
  have ham : subset_l a m.val := by
    rcases (hn a).mp ha with ha | ha
    · exact fun x hx => PowerlessNaturalOrder.member_transitive_l hℳ hω m.val hm a x ha hx
    · exact fun x hx => ha ▸ hx
  have hC := PowerlessLevyCertificateClosure.monotone_l hℳ hω ht.1 hT hm ham hc
  have hq := (PowerlessLevyCertificate.natural_l hc).2.2.2
  apply lower_complete_l hℳ hω ht hT hU hδ hωδ B hB h₁ hm hn p c f _ hf h
  rcases hq with hq | hq
  · exact Or.inl (hq ▸ hC)
  · exact Or.inr (hq ▸ hC)



/-- 后继接受的可靠性沿原证书递归，不要求前驱层任意极性完备。 -/
theorem source_l {R : carrier_l ℳ}
    (h𝒩 : Theory.Models (structure_l U hU₀) PowerlessFiniteStageEvaluation.theory_m)
    (hR : PowerlessEvaluationOperator.assignments_l ω.val U R)
    (hH : PowerlessEvaluationRecursion.evaluation_l ω.val e.val T.val U t₁.val t₂.val t₃.val R H)
    (hn : PowerlessNatural.successor_l m.val n.val) (p c f : type_l U)
    (h : (lift_m B).satisfies
      (env_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ n p c f)) :
    PowerlessTruthSign.sign_l e.val t₁.val H p.val c.val f.val := by
  let η := PowerlessTruthOracle.env_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ n p c f
  let w : Term ℒ [] PowerlessTruthOracle.context_m .set := .fvar .here
  let z : Term ℒ [] PowerlessTruthOracle.context_m .set := .fvar (.there .here)
  let V : Term ℒ [] PowerlessTruthOracle.context_m .set := .fvar (.there (.there .here))
  let s₁ : Term ℒ [] PowerlessTruthOracle.context_m .set := .fvar (.there (.there (.there .here)))
  let s₂ : Term ℒ [] PowerlessTruthOracle.context_m .set := .fvar (.there (.there (.there (.there .here))))
  let s₃ : Term ℒ [] PowerlessTruthOracle.context_m .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let v : Term ℒ [] PowerlessTruthOracle.context_m .set := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  let a : Term ℒ [] PowerlessTruthOracle.context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))
  let b : Term ℒ [] PowerlessTruthOracle.context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
  let g : Term ℒ [] PowerlessTruthOracle.context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
  let C := lower_m B w z V s₁ s₂ s₃ v a b g
  change (PowerlessTruthOracle.accepts_m C w z V s₁ s₂ s₃ v a b g).satisfies η at h
  apply PowerlessTruthOracle.accepts_source_l C hℳ hω ht hT hU hδ hωδ h𝒩 hR hH
    η w z V s₁ s₂ s₃ v a b g rfl rfl rfl rfl rfl rfl ?_ h
  intro p c f hC
  exact lower_sound_l hℳ hω ht hT hU hδ hωδ B hB hn p c f
    ((lower_formula_l B
      (PowerlessTruthOracle.env_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ n p c f)
      w z V s₁ s₂ s₃ v a b g).mp hC)


end YesMetaZFC.BMS.ConstructibleBridge.PowerlessPartialTruthSuccessor
