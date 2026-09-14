import BMSConstructibleBridge.PowerlessTruthRecordAbsolute
import BMSConstructibleBridge.PowerlessTruthSign
import BMSConstructibleBridge.PowerlessAmbientExistential

/-!
# 当前层中读取真子记录的存在量词规则

量词规则同时检查合法槽位、真实有限更新图与候选记录集中的真子记录。
结论只消费严格较小公式码的记录可靠性，不循环假设整张表已经可靠。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthExists

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

def rule_m {Γ Δ : SortContext ℒ} (ω e D f i b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let q (s : Term ℒ Γ Δ .set) := (s.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  PowerlessAmbientExistential.exists_m ω f i
    (PowerlessTruthRecord.entry_m (q D) (q e) (q b) (.bvar .here))

theorem source_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U δ R H c : carrier_l ℳ}
    {hU₀ : ∃ x, member_l ℳ x U} (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val)
    (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
    (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
    (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U)
    (hδ : PowerlessStagePair.limit_l δ)
    (hR : PowerlessEvaluationOperator.assignments_l ω.val U R)
    (hH : PowerlessEvaluationRecursion.evaluation_l ω.val e.val T.val U t₁.val t₂.val t₃.val R H)
    {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w z D f i b : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω.val) (hz : (z.eval η).val = e.val)
    (hD : ∀ d, member_l ℳ d c → ∀ p g,
      PowerlessTruthRecord.entry_l (D.eval η).val p d g → PowerlessTruthSign.sign_l e.val t₁.val H p d g)
    (hc : PowerlessFormulaConstructor.constructor_l ω.val e.val T.val t₃.val (i.eval η).val (b.eval η).val c)
    (h : (rule_m w z D f i b).satisfies η) :
    PowerlessEvaluationClause.query_l H c (f.eval η).val := by
  let q (s : Term ℒ Γ Δ .set) := (s.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  change (PowerlessAmbientAssignments.slot_m w f i).satisfies η ∧
    ∃ a g : type_l U,
      (PowerlessAmbientAssignments.finite_m (q w) (.bvar .here)).satisfies ((η.pushBound a).pushBound g) ∧
      (PowerlessAssignmentUpdate.update_m (q f) (q i) (.bvar (.there .here)) (.bvar .here)).satisfies
        ((η.pushBound a).pushBound g) ∧
      (PowerlessTruthRecord.entry_m (q D) (q z) (q b) (.bvar .here)).satisfies ((η.pushBound a).pushBound g) at h
  obtain ⟨hf, a, g, hg, hu, hq⟩ := h
  obtain ⟨n, hn, hf, hi⟩ :=
    (PowerlessStageAmbientAssignments.slot_source_l hℳ hω ht hT hU hδ η w f i hw).mp hf
  have hw₀ : ((q w).eval ((η.pushBound a).pushBound g)).val = ω.val := by
    simpa only [q, Term.eval_weakenBound] using hw
  have hg₀ := (PowerlessStageAmbientAssignments.finite_source_l hℳ hω ht hT hU hδ
    ((η.pushBound a).pushBound g) (q w) (.bvar .here) hw₀).mp hg
  have hu₀ := (PowerlessValueAbsolute.update_source_l hUT ((η.pushBound a).pushBound g)
    (q f) (q i) (.bvar (.there .here)) (.bvar .here)).mp hu
  have hq₀ := (PowerlessTruthRecordAbsolute.entry_source_l hUT ((η.pushBound a).pushBound g)
    (q D) (q z) (q b) (.bvar .here)).mp hq
  simp only [q, Term.eval_weakenBound] at hu₀ hq₀
  simp only [Term.eval, Env.pushBound, Assignment.push] at hg₀ hu₀ hq₀
  rw [hz] at hq₀
  obtain ⟨m, _, hg₀⟩ := hg₀
  have hnm := PowerlessAssignmentDomain.domain_l hℳ hf hg₀ hi hu₀
  subst m
  have hq₁ := (PowerlessTruthSign.positive_l (PowerlessEvaluationTags.distinct_l hℳ ht).1).mp
    (hD _ (PowerlessFormulaConstructor.bounds_l hℳ hω ht.1 hT hc).2 _ _ hq₀)
  exact (PowerlessEvaluationEquations.exists_l hℳ hω ht hT hH hc (f.eval η).val).mpr
    ⟨(hR (f.eval η).val).mpr ⟨n, hn, hf⟩, n, hn, hf, hi, a.val, a.property, g.val, hg₀, hu₀, hq₁⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthExists
