import BMSConstructibleBridge.PowerlessStageAmbientAssignments
import BMSConstructibleBridge.PowerlessStageBoundedTruth

/-!
# 当前域真值公式的存在量词步骤

量词见证和更新图均在当前域内部量化，完整域与求值器不是源公式参数。
先证明任意已解释正文的量词规则，再用实际有界真值公式填入正文；
此步不宣称已覆盖全部正层证书的递归闭包。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessAmbientExistential

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

/-- 正文的两个新增槽位依次为更新图 g 和量词见证 a。 -/
def exists_m {Γ Δ : SortContext ℒ} (ω f i : Term ℒ Γ Δ .set)
    (φ : Formula ℒ (.set :: .set :: Γ) Δ) : Formula ℒ Γ Δ :=
  let q (s : Term ℒ Γ Δ .set) := (s.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .conj (PowerlessAmbientAssignments.slot_m ω f i)
    (.existsE .set <| .existsE .set <|
      .conj (PowerlessAmbientAssignments.finite_m (q ω) (.bvar .here))
        (.conj (PowerlessAssignmentUpdate.update_m (q f) (q i) (.bvar (.there .here)) (.bvar .here)) φ))

def bounded_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ b f i : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let q (s : Term ℒ Γ Δ .set) := (s.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  exists_m ω f i (PowerlessBoundedTruth.truth_m (q ω) (q e) (q T) (q t₁) (q t₂) (q t₃) (q b) (.bvar .here))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U δ : carrier_l ℳ}
  {hU₀ : ∃ x, member_l ℳ x U} (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val)
  (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
  (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
  (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U)
  (hδ : PowerlessStagePair.limit_l δ) (hωδ : member_l ℳ ω.val δ)

include hℳ hω ht hT hU hδ hωδ

/-- 把已解释的实际正文接到量词子句；更新图的定义域由真实 map 条件辨认。 -/
theorem source_l {H b : carrier_l ℳ}
    {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w f i : Term ℒ Γ Δ .set) (hw : (w.eval η).val = ω.val)
    (φ : Formula ℒ (.set :: .set :: Γ) Δ)
    (hφ : ∀ a g : type_l U, (∃ n, member_l ℳ n ω.val ∧ map_l g.val n U) →
      (φ.satisfies ((η.pushBound a).pushBound g) ↔ PowerlessEvaluationClause.query_l H b g.val)) :
    (exists_m w f i φ).satisfies η ↔
      PowerlessEvaluationClause.exists_l ω.val U H (f.eval η).val (i.eval η).val b := by
  let q (s : Term ℒ Γ Δ .set) := (s.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  have h₀ : (exists_m w f i φ).satisfies η ↔
      (∃ n, member_l ℳ n ω.val ∧ map_l (f.eval η).val n U ∧ member_l ℳ (i.eval η).val n) ∧
        ∃ a g : type_l U, (∃ m, member_l ℳ m ω.val ∧ map_l g.val m U) ∧
          PowerlessAssignmentUpdate.update_l (f.eval η).val (i.eval η).val a.val g.val ∧
            PowerlessEvaluationClause.query_l H b g.val := by
    change ((PowerlessAmbientAssignments.slot_m w f i).satisfies η ∧
      ∃ a g : type_l U,
        (PowerlessAmbientAssignments.finite_m (q w) (.bvar .here)).satisfies ((η.pushBound a).pushBound g) ∧
        (PowerlessAssignmentUpdate.update_m (q f) (q i) (.bvar (.there .here)) (.bvar .here)).satisfies
          ((η.pushBound a).pushBound g) ∧ φ.satisfies ((η.pushBound a).pushBound g)) ↔ _
    rw [PowerlessStageAmbientAssignments.slot_source_l hℳ hω ht hT hU hδ η w f i hw]
    refine and_congr Iff.rfl (exists_congr fun a => exists_congr fun g => ?_)
    have hw₀ : ((q w).eval ((η.pushBound a).pushBound g)).val = ω.val := by
      simpa only [q, Term.eval_weakenBound] using hw
    have hg := PowerlessStageAmbientAssignments.finite_source_l hℳ hω ht hT hU hδ
      ((η.pushBound a).pushBound g) (q w) (.bvar .here) hw₀
    have hu := PowerlessValueAbsolute.update_source_l hUT ((η.pushBound a).pushBound g)
      (q f) (q i) (.bvar (.there .here)) (.bvar .here)
    simp only [q, Term.eval_weakenBound] at hg hu
    simp only [Term.eval, Env.pushBound, Assignment.push] at hg hu
    constructor
    · rintro ⟨h₁, h₂, h₃⟩
      have h₄ := hg.mp h₁
      exact ⟨h₄, hu.mp h₂, (hφ a g h₄).mp h₃⟩
    · rintro ⟨h₁, h₂, h₃⟩
      exact ⟨hg.mpr h₁, hu.mpr h₂, (hφ a g h₁).mpr h₃⟩
  refine h₀.trans ⟨?_, ?_⟩
  · rintro ⟨⟨n, hn, hf, hi⟩, a, g, ⟨m, _, hg⟩, hu, hq⟩
    have hnm := PowerlessAssignmentDomain.domain_l hℳ hf hg hi hu
    subst m
    exact ⟨n, hn, hf, hi, a.val, a.property, g.val, hg, hu, hq⟩
  · rintro ⟨n, hn, hf, hi, a, ha, g, hg, hu, hq⟩
    have hgU := PowerlessStageFiniteGraphs.finite_l hℳ hω ht hT hU hδ
      (fun x hx => PowerlessOrdinal.transitive_l hδ.1 ω.val x hωδ hx) n hn g hg
    exact ⟨⟨n, hn, hf, hi⟩, ⟨a, ha⟩, ⟨g, hgU⟩, ⟨n, hn, hg⟩, hu, hq⟩

variable (h𝒩 : Theory.Models (structure_l U hU₀) PowerlessFiniteStageEvaluation.theory_m)

include h𝒩

/-- 用已经证明的有界真值正文消去规则中的解释假设。 -/
theorem bounded_source_l {R H : carrier_l ℳ}
    (hR : PowerlessEvaluationOperator.assignments_l ω.val U R)
    (hH : PowerlessEvaluationRecursion.evaluation_l ω.val e.val T.val U t₁.val t₂.val t₃.val R H)
    {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w z V s₁ s₂ s₃ b f i : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω.val) (hz : (z.eval η).val = e.val) (hV : (V.eval η).val = T.val)
    (hs₁ : (s₁.eval η).val = t₁.val) (hs₂ : (s₂.eval η).val = t₂.val) (hs₃ : (s₃.eval η).val = t₃.val)
    (hb : PowerlessBoundedCertificate.recognizes_l ω.val e.val T.val t₁.val t₂.val t₃.val (b.eval η).val) :
    (bounded_m w z V s₁ s₂ s₃ b f i).satisfies η ↔
      PowerlessEvaluationClause.exists_l ω.val U H (f.eval η).val (i.eval η).val (b.eval η).val := by
  let q (s : Term ℒ Γ Δ .set) := (s.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  apply source_l hℳ hω ht hT hU hδ hωδ η w f i hw
    (PowerlessBoundedTruth.truth_m (q w) (q z) (q V) (q s₁) (q s₂) (q s₃) (q b) (.bvar .here))
  intro a g hg
  have h := PowerlessStageBoundedTruth.source_l hℳ hω ht hT hU hδ hωδ h𝒩 hR hH
    ((η.pushBound a).pushBound g) (q w) (q z) (q V) (q s₁) (q s₂) (q s₃) (q b) (.bvar .here)
    (by simpa only [q, Term.eval_weakenBound] using hw)
    (by simpa only [q, Term.eval_weakenBound] using hz)
    (by simpa only [q, Term.eval_weakenBound] using hV)
    (by simpa only [q, Term.eval_weakenBound] using hs₁)
    (by simpa only [q, Term.eval_weakenBound] using hs₂)
    (by simpa only [q, Term.eval_weakenBound] using hs₃)
    (by simpa only [q, Term.eval_weakenBound] using hb) hg
  simp only [q, Term.eval_weakenBound] at h
  simpa only [q, Term.eval, Env.pushBound, Assignment.push] using h

/-- 与原存在构造子的完整求值一致，不预先假定赋值或槽位合法。 -/
theorem query_l {R H c : carrier_l ℳ}
    (hR : PowerlessEvaluationOperator.assignments_l ω.val U R)
    (hH : PowerlessEvaluationRecursion.evaluation_l ω.val e.val T.val U t₁.val t₂.val t₃.val R H)
    {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w z V s₁ s₂ s₃ b f i : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω.val) (hz : (z.eval η).val = e.val) (hV : (V.eval η).val = T.val)
    (hs₁ : (s₁.eval η).val = t₁.val) (hs₂ : (s₂.eval η).val = t₂.val) (hs₃ : (s₃.eval η).val = t₃.val)
    (hb : PowerlessBoundedCertificate.recognizes_l ω.val e.val T.val t₁.val t₂.val t₃.val (b.eval η).val)
    (hc : PowerlessFormulaConstructor.constructor_l ω.val e.val T.val t₃.val (i.eval η).val (b.eval η).val c) :
    (bounded_m w z V s₁ s₂ s₃ b f i).satisfies η ↔
      PowerlessEvaluationClause.query_l H c (f.eval η).val := by
  refine (bounded_source_l hℳ hω ht hT hU hδ hωδ h𝒩 hR hH η
    w z V s₁ s₂ s₃ b f i hw hz hV hs₁ hs₂ hs₃ hb).trans ⟨?_, ?_⟩
  · intro h
    have hf : member_l ℳ (f.eval η).val R := by
      obtain ⟨n, hn, hf, _⟩ := h
      exact (hR (f.eval η).val).mpr ⟨n, hn, hf⟩
    exact (PowerlessEvaluationEquations.exists_l hℳ hω ht hT hH hc (f.eval η).val).mpr
      ⟨hf, h⟩
  · intro h
    exact ((PowerlessEvaluationEquations.exists_l hℳ hω ht hT hH hc (f.eval η).val).mp h).2

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessAmbientExistential
