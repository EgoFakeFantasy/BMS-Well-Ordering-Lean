import BMSConstructibleBridge.PowerlessPartialTruthZero
import BMSConstructibleBridge.PowerlessOracleIntroduction
import BMSConstructibleBridge.PowerlessOracleParameters

/-!
# 有限核心支持下的后继部分真值引入

原有界证书进入任意后继层，不要求小层完整核心。支持实例的参数
是后继层实际调用的低层矩阵，而不是被调用的部分真值公式本身。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessPartialTruthIntroduction

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure PowerlessPartialTruth PowerlessTruthOracle

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

/-- 后继公式实际使用的十参数低层矩阵。 -/
def oracle_m (B : Formula ℒ [] context_m) : Formula ℒ [] context_m :=
  let ω : Term ℒ [] context_m .set := .fvar .here
  let e : Term ℒ [] context_m .set := .fvar (.there .here)
  let T : Term ℒ [] context_m .set := .fvar (.there (.there .here))
  let t₁ : Term ℒ [] context_m .set := .fvar (.there (.there (.there .here)))
  let t₂ : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there .here))))
  let t₃ : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let n : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  let p : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))
  let c : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
  let f : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
  lower_m B ω e T t₁ t₂ t₃ n p c f

theorem oracle_formula_l (B : Formula ℒ [] context_m)
    {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e T t₁ t₂ t₃ n p c f : carrier_l ℳ) :
    (oracle_m B).satisfies (env_l ω e T t₁ t₂ t₃ n p c f) ↔
      PowerlessPartialTruth.lower_l B ω e T t₁ t₂ t₃ n p c f := by
  unfold oracle_m
  exact lower_formula_l B (env_l ω e T t₁ t₂ t₃ n p c f) _ _ _ _ _ _ _ _ _ _

theorem lift_formula_l (B : Formula ℒ [] context_m)
    {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e T t₁ t₂ t₃ n p c f : carrier_l ℳ) :
    (lift_m B).satisfies (env_l ω e T t₁ t₂ t₃ n p c f) ↔
      PowerlessOracleParameters.accepts_l (oracle_m B) ω e T t₁ t₂ t₃ n p c f := by
  unfold lift_m
  exact PowerlessOracleParameters.accepts_formula_l (oracle_m B)
    (env_l ω e T t₁ t₂ t₃ n p c f) _ _ _ _ _ _ _ _ _ _

/-- 实际低层矩阵经有限支持进入后继证书，不要求结构满足完整核心。 -/
theorem lower_l (B : Formula ℒ [] context_m)
    {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ (PowerlessOracleIntroduction.theory_m (oracle_m B)))
    (ω e T t₁ t₂ t₃ n p c f : carrier_l ℳ) (hc : member_l ℳ c ω)
    (h : (oracle_m B).satisfies (env_l ω e T t₁ t₂ t₃ n p c f)) :
    (lift_m B).satisfies (env_l ω e T t₁ t₂ t₃ n p c f) := by
  have hI := PowerlessOracleIntroduction.satisfies_l (oracle_m B) hℳ
    (env_l ω e T t₁ t₂ t₃ n p c f)
  refine hI hc (Or.inl ?_)
  exact (instance_formula_l (oracle_m B) _ _ _ _ _ _ _ _ _ _ _).mpr h

/-- 前驱层匹配极性的双向正确性产生后继层两种标记的实际证书。 -/
theorem successor_l (B : Formula ℒ [] context_m)
    {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ (PowerlessOracleIntroduction.theory_m (oracle_m B)))
    {ω e T t₁ t₂ t₃ m n p c f : carrier_l ℳ} {P : Prop}
    (hm : member_l ℳ m ω) (hn : PowerlessNatural.successor_l m n)
    (hc : member_l ℳ c ω) (hf : PowerlessAmbientAssignments.finite_l ω f)
    (hC : PowerlessLevyCertificate.class_l ω e T t₁ t₂ t₃ c m e ∨
      PowerlessLevyCertificate.class_l ω e T t₁ t₂ t₃ c m t₁)
    (h₀ : PowerlessLevyCertificate.class_l ω e T t₁ t₂ t₃ c m e →
      (B.satisfies (env_l ω e T t₁ t₂ t₃ m e c f) ↔ P))
    (h₁ : PowerlessLevyCertificate.class_l ω e T t₁ t₂ t₃ c m t₁ →
      (B.satisfies (env_l ω e T t₁ t₂ t₃ m t₁ c f) ↔ ¬P))
    (h : (p = e ∧ P) ∨ (p = t₁ ∧ ¬P)) :
    (lift_m B).satisfies (env_l ω e T t₁ t₂ t₃ n p c f) := by
  apply lower_l B hℳ ω e T t₁ t₂ t₃ n p c f hc
  exact (oracle_formula_l B ω e T t₁ t₂ t₃ n p c f).mpr
    (lower_complete_l B hm hn hf hC h₀ h₁ h)

/-- 原零层证书经实际局部引入闭句进入后继层。 -/
theorem original_l (B : Formula ℒ [] context_m)
    {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ (PowerlessOracleIntroduction.theory_m (oracle_m B)))
    (ω e T t₁ t₂ t₃ n p c f : carrier_l ℳ) (hc : member_l ℳ c ω)
    (h : (PowerlessPartialTruth.formula_m 0).satisfies (env_l ω e T t₁ t₂ t₃ n p c f)) :
    (lift_m B).satisfies (env_l ω e T t₁ t₂ t₃ n p c f) := by
  have hI := PowerlessOracleIntroduction.satisfies_l (oracle_m B) hℳ (env_l ω e T t₁ t₂ t₃ n p c f)
  exact hI hc (Or.inr (Or.inl h))

/-- 全部内部有界代码及层内有限赋值的后继接受，不预设推进条件。 -/
theorem bounded_l (B : Formula ℒ [] context_m) {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U δ R H : carrier_l ℳ}
    {hU₀ : ∃ x, member_l ℳ x U} (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ n : type_l U} (hω : omega_l ω.val)
    (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
    (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
    (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U)
    (hδ : PowerlessStagePair.limit_l δ) (hωδ : member_l ℳ ω.val δ)
    (h𝒩 : Theory.Models (structure_l U hU₀) PowerlessFiniteStageEvaluation.theory_m)
    (h₀ : Theory.Models (structure_l U hU₀) PowerlessTruthIntroduction.theory_m)
    (h₁ : Theory.Models (structure_l U hU₀) (PowerlessOracleIntroduction.theory_m (oracle_m B)))
    (hR : PowerlessEvaluationOperator.assignments_l ω.val U R)
    (hH : PowerlessEvaluationRecursion.evaluation_l ω.val e.val T.val U t₁.val t₂.val t₃.val R H)
    (p c f : type_l U)
    (hc : PowerlessBoundedCertificate.recognizes_l ω.val e.val T.val t₁.val t₂.val t₃.val c.val)
    (hf : ∃ n, member_l ℳ n ω.val ∧ map_l f.val n U)
    (h : PowerlessTruthSign.sign_l e.val t₁.val H p.val c.val f.val) :
    (PowerlessPartialTruth.lift_m B).satisfies
      (PowerlessTruthOracle.env_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ n p c f) := by
  have hc₀ : member_l ℳ c.val ω.val := by
    obtain ⟨D, hD, hc⟩ := hc
    exact PowerlessBoundedCertificate.natural_l hℳ hω hD hc
  exact original_l B h₁ ω e T t₁ t₂ t₃ n p c f hc₀
    ((PowerlessPartialTruthZero.source_l hℳ hω ht hT hU hδ hωδ h𝒩 h₀ hR hH p c f hc hf).mpr h)


/-- 第一层内的严格升层回到零层，不使用同一码的归纳假设。 -/
theorem promotion_l (B : Formula ℒ [] context_m) {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U δ R H : carrier_l ℳ}
    {hU₀ : ∃ x, member_l ℳ x U} (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ n : type_l U} (hω : omega_l ω.val)
    (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
    (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
    (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U)
    (hδ : PowerlessStagePair.limit_l δ) (hωδ : member_l ℳ ω.val δ)
    (h𝒩 : Theory.Models (structure_l U hU₀) PowerlessFiniteStageEvaluation.theory_m)
    (h₀ : Theory.Models (structure_l U hU₀) PowerlessTruthIntroduction.theory_m)
    (h₁ : Theory.Models (structure_l U hU₀) (PowerlessOracleIntroduction.theory_m (oracle_m B)))
    (hR : PowerlessEvaluationOperator.assignments_l ω.val U R)
    (hH : PowerlessEvaluationRecursion.evaluation_l ω.val e.val T.val U t₁.val t₂.val t₃.val R H)
    (p c f : type_l U) {m q : carrier_l ℳ}
    (hn : subset_l n.val t₁.val) (hm : member_l ℳ m n.val)
    (hc : PowerlessLevyCertificate.class_l ω.val e.val T.val t₁.val t₂.val t₃.val c.val m q)
    (hf : ∃ n, member_l ℳ n ω.val ∧ map_l f.val n U)
    (h : PowerlessTruthSign.sign_l e.val t₁.val H p.val c.val f.val) :
    (PowerlessPartialTruth.lift_m B).satisfies
      (PowerlessTruthOracle.env_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ n p c f) := by
  have hm₀ : m = e.val := by
    rcases (ht.2.1 m).mp (hn m hm) with hm | hm
    · exact (ht.1 m hm).elim
    · exact hm
  rw [hm₀] at hc
  exact bounded_l B hℳ hω ht hT hU hδ hωδ h𝒩 h₀ h₁ hR hH p c f
    (PowerlessLevyZero.class_l hℳ hω ht.1 hT hc) hf h

attribute [local irreducible] lower_m PowerlessOracleParameters.accepts_l
  PowerlessTruthOracle.accepts_m

/-- 与非规则只消费各子式的实际接受，不要求它们共用证书。 -/
theorem nand_l (B : Formula ℒ [] context_m)
    {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ (PowerlessOracleIntroduction.theory_m (oracle_m B)))
    (ω e T t₁ t₂ t₃ n p c f a b : carrier_l ℳ) (hc : member_l ℳ c ω)
    (hC : PowerlessFormulaConstructor.constructor_l ω e T t₂ a b c)
    (hf : PowerlessAmbientAssignments.finite_l ω f)
    (h : (p = e ∧
      ((lift_m B).satisfies (env_l ω e T t₁ t₂ t₃ n t₁ a f) ∨
       (lift_m B).satisfies (env_l ω e T t₁ t₂ t₃ n t₁ b f))) ∨
      (p = t₁ ∧
       (lift_m B).satisfies (env_l ω e T t₁ t₂ t₃ n e a f) ∧
       (lift_m B).satisfies (env_l ω e T t₁ t₂ t₃ n e b f))) :
    (lift_m B).satisfies (env_l ω e T t₁ t₂ t₃ n p c f) := by
  have hI := PowerlessOracleIntroduction.satisfies_l (oracle_m B) hℳ (env_l ω e T t₁ t₂ t₃ n p c f)
  refine hI hc (Or.inr (Or.inr (Or.inl ⟨a, b, ?_, ?_⟩)))
  · exact (PowerlessFormulaConstructor.constructor_formula_l _ _ _ _ _ _ _ _).mpr hC
  · apply (PowerlessOracleParameters.nand_formula_l (oracle_m B) _ _ _ _ _ _ _ _ _ _ _ _).mpr
    refine ⟨hf, ?_⟩
    simp only [lift_formula_l] at h
    simp only [Term.eval_weakenBound]
    simpa only [env_l, Term.eval, Env.pushBound, Env.pushFree, Assignment.push] using h


/-- 正无界存在使用一个真实更新图及其子式接受。 -/
theorem exists_l (B : Formula ℒ [] context_m)
    {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ (PowerlessOracleIntroduction.theory_m (oracle_m B)))
    (ω e T t₁ t₂ t₃ n c f i b a g : carrier_l ℳ) (hc : member_l ℳ c ω)
    (hC : PowerlessFormulaConstructor.constructor_l ω e T t₃ i b c)
    (hi : PowerlessAmbientAssignments.slot_l ω f i)
    (hg : PowerlessAmbientAssignments.finite_l ω g)
    (hfg : PowerlessAssignmentUpdate.update_l f i a g)
    (h : (lift_m B).satisfies (env_l ω e T t₁ t₂ t₃ n e b g)) :
    (lift_m B).satisfies (env_l ω e T t₁ t₂ t₃ n e c f) := by
  have hI := PowerlessOracleIntroduction.satisfies_l (oracle_m B) hℳ (env_l ω e T t₁ t₂ t₃ n e c f)
  refine hI hc (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, i, b, ?_, ?_⟩))))
  · exact (PowerlessFormulaConstructor.constructor_formula_l _ _ _ _ _ _ _ _).mpr hC
  · apply (PowerlessOracleParameters.existential_formula_l (oracle_m B) _ _ _ _ _ _ _ _ _ _ _).mpr
    refine ⟨hi, a, g, hg, hfg, ?_⟩
    rw [lift_formula_l] at h
    simp only [Term.eval_weakenBound]
    simpa only [env_l, Term.eval, Env.pushBound, Env.pushFree, Assignment.push] using h

/-- 有界真分支只选取一个界内元素及其实际更新图。 -/
theorem positive_l (B : Formula ℒ [] context_m)
    {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ (PowerlessOracleIntroduction.theory_m (oracle_m B)))
    (ω e T t₁ t₂ t₃ n c f i j b z a g : carrier_l ℳ) (hc : member_l ℳ c ω)
    (hC : PowerlessBoundedCode.code_l ω e T t₂ t₃ i j b c)
    (hi : PowerlessAmbientAssignments.slot_l ω f i) (hz : value_l f j z)
    (ha : member_l ℳ a z) (hg : PowerlessAmbientAssignments.finite_l ω g)
    (hfg : PowerlessAssignmentUpdate.update_l f i a g)
    (h : (lift_m B).satisfies (env_l ω e T t₁ t₂ t₃ n e b g)) :
    (lift_m B).satisfies (env_l ω e T t₁ t₂ t₃ n e c f) := by
  have hI := PowerlessOracleIntroduction.satisfies_l (oracle_m B) hℳ (env_l ω e T t₁ t₂ t₃ n e c f)
  refine hI hc (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, j, b, ?_, Or.inl ⟨rfl, ?_⟩⟩))))
  · exact (PowerlessBoundedCode.code_formula_l _ _ _ _ _ _ _ _ _ _).mpr hC
  · apply (PowerlessOracleParameters.positive_formula_l (oracle_m B) _ _ _ _ _ _ _ _ _ _ _ _).mpr
    refine ⟨hi, z, hz, a, ha, g, hg, hfg, ?_⟩
    rw [lift_formula_l] at h
    simp only [Term.eval_weakenBound]
    simpa only [env_l, Term.eval, Env.pushBound, Env.pushFree, Assignment.push] using h

/-- 有界假分支保留非法槽及对整个界集合的全称条件。 -/
theorem negative_l (B : Formula ℒ [] context_m)
    {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ (PowerlessOracleIntroduction.theory_m (oracle_m B)))
    (ω e T t₁ t₂ t₃ n c f i j b : carrier_l ℳ) (hc : member_l ℳ c ω)
    (hC : PowerlessBoundedCode.code_l ω e T t₂ t₃ i j b c)
    (hf : PowerlessAmbientAssignments.finite_l ω f)
    (h : ¬ PowerlessAmbientAssignments.slot_l ω f i ∨
      ∀ z, value_l f j z → ∀ a, member_l ℳ a z → ∃ g,
        PowerlessAmbientAssignments.finite_l ω g ∧ PowerlessAssignmentUpdate.update_l f i a g ∧
          (lift_m B).satisfies (env_l ω e T t₁ t₂ t₃ n t₁ b g)) :
    (lift_m B).satisfies (env_l ω e T t₁ t₂ t₃ n t₁ c f) := by
  have hI := PowerlessOracleIntroduction.satisfies_l (oracle_m B) hℳ (env_l ω e T t₁ t₂ t₃ n t₁ c f)
  refine hI hc (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, j, b, ?_, Or.inr ⟨rfl, ?_⟩⟩))))
  · exact (PowerlessBoundedCode.code_formula_l _ _ _ _ _ _ _ _ _ _).mpr hC
  · apply (PowerlessOracleParameters.negative_formula_l (oracle_m B) _ _ _ _ _ _ _ _ _ _ _ _).mpr
    refine ⟨hf, ?_⟩
    simp only [lift_formula_l] at h
    simp only [Term.eval_weakenBound]
    simpa only [PowerlessOracleParameters.witness_l, env_l, Term.eval,
      Env.pushBound, Env.pushFree, Assignment.push] using h
end YesMetaZFC.BMS.ConstructibleBridge.PowerlessPartialTruthIntroduction
