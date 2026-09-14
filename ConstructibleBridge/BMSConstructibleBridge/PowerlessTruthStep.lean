import BMSConstructibleBridge.PowerlessTruthBase
import BMSConstructibleBridge.PowerlessTruthNand
import BMSConstructibleBridge.PowerlessTruthExists
import BMSConstructibleBridge.PowerlessTruthBounded
import BMSConstructibleBridge.PowerlessBoundedCertificateAbsolute
import BMSConstructibleBridge.PowerlessStageAdditionIteration

/-!
# 不含全局真值参数的局部证书规则

基例检查原有界公式识别；其余三类检查同一原构造子及候选记录。
源公式不含当前域 U、高度 δ 或完整求值图 H。
局部可靠性只使用严格较小子码的记录可靠性，不假定整表可靠。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthStep

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

def step_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ D p c f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let q (s : Term ℒ Γ Δ .set) := (s.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  let r (s : Term ℒ Γ Δ .set) := (q s).weakenBound SetTheory.SetSort.set
  .disj
    (.conj (PowerlessBoundedCertificate.recognizes_m ω e T t₁ t₂ t₃ c)
      (PowerlessTruthBase.rule_m ω e T t₁ t₂ t₃ p c f))
    (.disj
      (.existsE .set (.existsE .set (.conj
        (PowerlessFormulaConstructor.constructor_m (q ω) (q e) (q T) (q t₂)
          (.bvar (.there .here)) (.bvar .here) (q c))
        (PowerlessTruthNand.rule_m (q ω) (q e) (q t₁) (q D) (q p)
          (.bvar (.there .here)) (.bvar .here) (q f)))))
      (.disj
        (.conj (.equal p e) (.existsE .set (.existsE .set (.conj
          (PowerlessFormulaConstructor.constructor_m (q ω) (q e) (q T) (q t₃)
            (.bvar (.there .here)) (.bvar .here) (q c))
          (PowerlessTruthExists.rule_m (q ω) (q e) (q D) (q f)
            (.bvar (.there .here)) (.bvar .here))))))
        (.existsE .set (.existsE .set (.existsE .set (.conj
          (PowerlessBoundedCode.code_m (r ω) (r e) (r T) (r t₂) (r t₃)
            (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here) (r c))
          (PowerlessTruthBounded.rule_m (r ω) (r e) (r t₁) (r D) (r p)
            (.bvar .here) (r f) (.bvar (.there (.there .here))) (.bvar (.there .here)))))))))

theorem source_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U δ R H : carrier_l ℳ}
    {hU₀ : ∃ x, member_l ℳ x U} (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val)
    (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
    (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
    (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U)
    (hδ : PowerlessStagePair.limit_l δ) (hωδ : member_l ℳ ω.val δ)
    (h𝒩 : Theory.Models (structure_l U hU₀) PowerlessFiniteStageEvaluation.theory_m)
    (hR : PowerlessEvaluationOperator.assignments_l ω.val U R)
    (hH : PowerlessEvaluationRecursion.evaluation_l ω.val e.val T.val U t₁.val t₂.val t₃.val R H)
    {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w z V s₁ s₂ s₃ D p c f : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω.val) (hz : (z.eval η).val = e.val) (hV : (V.eval η).val = T.val)
    (hs₁ : (s₁.eval η).val = t₁.val) (hs₂ : (s₂.eval η).val = t₂.val) (hs₃ : (s₃.eval η).val = t₃.val)
    (hD : ∀ d, member_l ℳ d (c.eval η).val → ∀ a g,
      PowerlessTruthRecord.entry_l (D.eval η).val a d g →
        PowerlessTruthSign.sign_l e.val t₁.val H a d g)
    (h : (step_m w z V s₁ s₂ s₃ D p c f).satisfies η) :
    PowerlessTruthSign.sign_l e.val t₁.val H (p.eval η).val (c.eval η).val (f.eval η).val := by
  let q (s : Term ℒ Γ Δ .set) := (s.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  let r (s : Term ℒ Γ Δ .set) := (q s).weakenBound SetTheory.SetSort.set
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  have hI := fun a ha F hF => PowerlessStageAdditionIteration.limit_l hℳ hω ht hT hU hωδ hδ (a := a) (F := F) ha hF
  have hw₀ : w.eval η = ω := Subtype.ext hw
  have hz₀ : z.eval η = e := Subtype.ext hz
  have hV₀ : V.eval η = T := Subtype.ext hV
  change
    ((PowerlessBoundedCertificate.recognizes_m w z V s₁ s₂ s₃ c).satisfies η ∧
      (PowerlessTruthBase.rule_m w z V s₁ s₂ s₃ p c f).satisfies η) ∨
    (∃ a b : type_l U,
      (PowerlessFormulaConstructor.constructor_m (q w) (q z) (q V) (q s₂)
        (.bvar (.there .here)) (.bvar .here) (q c)).satisfies ((η.pushBound a).pushBound b) ∧
      (PowerlessTruthNand.rule_m (q w) (q z) (q s₁) (q D) (q p)
        (.bvar (.there .here)) (.bvar .here) (q f)).satisfies ((η.pushBound a).pushBound b)) ∨
    (p.eval η = z.eval η ∧ ∃ i b : type_l U,
      (PowerlessFormulaConstructor.constructor_m (q w) (q z) (q V) (q s₃)
        (.bvar (.there .here)) (.bvar .here) (q c)).satisfies ((η.pushBound i).pushBound b) ∧
      (PowerlessTruthExists.rule_m (q w) (q z) (q D) (q f)
        (.bvar (.there .here)) (.bvar .here)).satisfies ((η.pushBound i).pushBound b)) ∨
    (∃ i j b : type_l U,
      (PowerlessBoundedCode.code_m (r w) (r z) (r V) (r s₂) (r s₃)
        (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here) (r c)).satisfies
          (((η.pushBound i).pushBound j).pushBound b) ∧
      (PowerlessTruthBounded.rule_m (r w) (r z) (r s₁) (r D) (r p)
        (.bvar .here) (r f) (.bvar (.there (.there .here))) (.bvar (.there .here))).satisfies
          (((η.pushBound i).pushBound j).pushBound b)) at h
  rcases h with ⟨hc, hf⟩ | ⟨a, b, hc, hf⟩ | ⟨hp, i, b, hc, hf⟩ | ⟨i, j, b, hc, hf⟩
  · rw [PowerlessBoundedCertificate.recognizes_formula_l, hw₀, hz₀, hV₀] at hc
    obtain ⟨A, hA, hc⟩ := hc
    have hc₀ := (PowerlessBoundedCertificateAbsolute.certificate_l hℳ hUT hω ht.1 hT hI).mp hA
    rw [hs₁, hs₂, hs₃] at hc₀
    exact ((PowerlessTruthBase.source_l hℳ hω ht hT hU hδ hωδ h𝒩 hR hH
      η w z V s₁ s₂ s₃ p c f hw hz hV hs₁ hs₂ hs₃ ⟨A.val, hc₀, hc⟩).mp hf).2
  · have hc₀ := (PowerlessFormulaCodeAbsolute.constructor_source_l hℳ hUT hω ht.1 hT hI
      ((η.pushBound a).pushBound b) (q w) (q z) (q V) (q s₂)
      (.bvar (.there .here)) (.bvar .here) (q c)
      (by simpa only [q, Term.eval_weakenBound] using hw₀)
      (by simpa only [q, Term.eval_weakenBound] using hz₀)
      (by simpa only [q, Term.eval_weakenBound] using hV₀)).mp hc
    simp only [q, Term.eval_weakenBound, hs₂] at hc₀
    have h₀ := PowerlessTruthNand.source_l hℳ hω ht hT hU hδ hR hH
      ((η.pushBound a).pushBound b) (q w) (q z) (q s₁) (q D) (q p)
      (.bvar (.there .here)) (.bvar .here) (q f)
      (by simpa only [q, Term.eval_weakenBound] using hw)
      (by simpa only [q, Term.eval_weakenBound] using hz)
      (by simpa only [q, Term.eval_weakenBound] using hs₁)
      (by simpa only [q, Term.eval_weakenBound] using hD) hc₀ hf
    simpa only [q, Term.eval_weakenBound] using h₀
  · have hc₀ := (PowerlessFormulaCodeAbsolute.constructor_source_l hℳ hUT hω ht.1 hT hI
      ((η.pushBound i).pushBound b) (q w) (q z) (q V) (q s₃)
      (.bvar (.there .here)) (.bvar .here) (q c)
      (by simpa only [q, Term.eval_weakenBound] using hw₀)
      (by simpa only [q, Term.eval_weakenBound] using hz₀)
      (by simpa only [q, Term.eval_weakenBound] using hV₀)).mp hc
    simp only [q, Term.eval_weakenBound, hs₃] at hc₀
    have h₀ := PowerlessTruthExists.source_l hℳ hω ht hT hU hδ hR hH
      ((η.pushBound i).pushBound b) (q w) (q z) (q D) (q f)
      (.bvar (.there .here)) (.bvar .here)
      (by simpa only [q, Term.eval_weakenBound] using hw)
      (by simpa only [q, Term.eval_weakenBound] using hz)
      (by simpa only [q, Term.eval_weakenBound] using hD) hc₀ hf
    exact Or.inl ⟨(congrArg Subtype.val hp).trans hz,
      by simpa only [q, Term.eval_weakenBound] using h₀⟩
  · rw [PowerlessBoundedCode.code_formula_l] at hc
    simp only [r, q, Term.eval_weakenBound, hw₀, hz₀, hV₀] at hc
    have hc₀ := (PowerlessBoundedCodeAbsolute.code_l hℳ hUT hω ht.1 hT hI).mp hc
    simp only [hs₂, hs₃] at hc₀
    have h₀ := PowerlessTruthBounded.source_l hℳ hω ht hT hU hδ hR hH
      (((η.pushBound i).pushBound j).pushBound b)
      (r w) (r z) (r s₁) (r D) (r p) (.bvar .here) (r f)
      (.bvar (.there (.there .here))) (.bvar (.there .here))
      (by simpa only [r, q, Term.eval_weakenBound] using hw)
      (by simpa only [r, q, Term.eval_weakenBound] using hz)
      (by simpa only [r, q, Term.eval_weakenBound] using hs₁)
      (by simpa only [r, q, Term.eval_weakenBound] using hD) hc₀ hf
    simpa only [r, q, Term.eval_weakenBound] using h₀

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthStep
