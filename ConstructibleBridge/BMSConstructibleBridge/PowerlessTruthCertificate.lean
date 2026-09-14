import BMSConstructibleBridge.PowerlessTruthStep

/-!
# 集合大小的局部真值证书及内部可靠性

每一成员必须是合法记录，其公式码属于内部 ω，且满足同一局部规则。
证书检查不含完整求值图 H；H 只出现在可靠性的后置性质中。
内部码归纳允许记录集是任意集合，不假定模型 ω 外部标准或良基。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthCertificate

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

def certificate_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ D : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let q (s : Term ℒ Γ Δ .set) := (((s.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
    ).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .forallE .set (.imp
    (SecondOrderObjectSyntax.member_m (.bvar .here) (D.weakenBound SetTheory.SetSort.set))
    (.existsE .set (.existsE .set (.existsE .set (.conj
      (PowerlessTruthRecord.record_m (.bvar (.there (.there .here))) (.bvar (.there .here))
        (.bvar .here) (.bvar (.there (.there (.there .here)))))
      (.conj (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (q ω))
        (PowerlessTruthStep.step_m (q ω) (q e) (q T) (q t₁) (q t₂) (q t₃) (q D)
          (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))))))))

def accepts_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ p c f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let q (s : Term ℒ Γ Δ .set) := s.weakenBound SetTheory.SetSort.set
  .existsE .set (.conj (certificate_m (q ω) (q e) (q T) (q t₁) (q t₂) (q t₃) (.bvar .here))
    (PowerlessTruthRecord.entry_m (.bvar .here) (q p) (q c) (q f)))

theorem sound_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U δ R H : carrier_l ℳ}
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
    (w z V s₁ s₂ s₃ D : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω.val) (hz : (z.eval η).val = e.val) (hV : (V.eval η).val = T.val)
    (hs₁ : (s₁.eval η).val = t₁.val) (hs₂ : (s₂.eval η).val = t₂.val) (hs₃ : (s₃.eval η).val = t₃.val)
    (hD : (certificate_m w z V s₁ s₂ s₃ D).satisfies η) :
    PowerlessTruthSign.valid_l e.val t₁.val H (D.eval η).val := by
  let q (s : Term ℒ Γ Δ .set) := (((s.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
    ).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  change ∀ r : type_l U,
    member_l (structure_l U hU₀) r ((D.weakenBound SetTheory.SetSort.set).eval (η.pushBound r)) →
    ∃ p c f : type_l U, PowerlessTruthRecord.record_l (ℳ := structure_l U hU₀) p c f r ∧
      member_l (structure_l U hU₀) c ((q w).eval ((((η.pushBound r).pushBound p).pushBound c).pushBound f)) ∧
      (PowerlessTruthStep.step_m (q w) (q z) (q V) (q s₁) (q s₂) (q s₃) (q D)
        (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)).satisfies
          ((((η.pushBound r).pushBound p).pushBound c).pushBound f) at hD
  have h₀ : ∀ p c f, PowerlessTruthRecord.entry_l (D.eval η).val p c f →
      member_l ℳ c ω.val ∧
      ((∀ d, member_l ℳ d c → ∀ a g,
        PowerlessTruthRecord.entry_l (D.eval η).val a d g →
          PowerlessTruthSign.sign_l e.val t₁.val H a d g) →
        PowerlessTruthSign.sign_l e.val t₁.val H p c f) := by
    rintro p c f ⟨r, hr, hc⟩
    let r₀ : type_l U := ⟨r, hUT (D.eval η).val r (D.eval η).property hr⟩
    have hr₁ : member_l (structure_l U hU₀) r₀
        ((D.weakenBound SetTheory.SetSort.set).eval (η.pushBound r₀)) := by
      rw [Term.eval_weakenBound]
      exact hr
    obtain ⟨p₀, c₀, f₀, h₁, hn, h₂⟩ := hD r₀ hr₁
    have h₁ := (PowerlessTruthRecordAbsolute.record_l hUT).mp h₁
    obtain ⟨rfl, rfl, rfl⟩ := PowerlessTruthRecord.injective_l hℳ hc h₁
    simp only [q, Term.eval_weakenBound] at hn
    change member_l ℳ c₀.val (w.eval η).val at hn
    rw [hw] at hn
    refine ⟨hn, ?_⟩
    intro h₃
    have h₄ := PowerlessTruthStep.source_l hℳ hω ht hT hU hδ hωδ h𝒩 hR hH
      ((((η.pushBound r₀).pushBound p₀).pushBound c₀).pushBound f₀)
      (q w) (q z) (q V) (q s₁) (q s₂) (q s₃) (q D)
      (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)
      (by simpa only [q, Term.eval_weakenBound] using hw)
      (by simpa only [q, Term.eval_weakenBound] using hz)
      (by simpa only [q, Term.eval_weakenBound] using hV)
      (by simpa only [q, Term.eval_weakenBound] using hs₁)
      (by simpa only [q, Term.eval_weakenBound] using hs₂)
      (by simpa only [q, Term.eval_weakenBound] using hs₃)
      (by
        simp only [q, Term.eval_weakenBound]
        exact h₃) h₂
    exact h₄
  let ζ : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 4 :=
    { bound := Fin.cases e.val (Fin.cases t₁.val (Fin.cases H (fun _ => (D.eval η).val))),
      free := fun _ => U }
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] :=
    .forallE .set (.forallE .set (.imp
      (PowerlessTruthRecord.entry_m (.fvar (.there (.there (.there (.there .here)))))
        (.bvar (.there .here)) (.fvar .here) (.bvar .here))
      (PowerlessTruthSign.sign_m (.fvar (.there .here)) (.fvar (.there (.there .here)))
        (.fvar (.there (.there (.there .here)))) (.bvar (.there .here)) (.fvar .here) (.bvar .here))))
  have hφ (c : carrier_l ℳ) : φ.satisfies ((PowerlessComprehension.env_l ζ).pushFree c) ↔
      ∀ p f, PowerlessTruthRecord.entry_l (D.eval η).val p c f →
        PowerlessTruthSign.sign_l e.val t₁.val H p c f := by
    simp only [φ, Formula.satisfies, PowerlessTruthRecord.entry_formula_l, PowerlessTruthSign.sign_formula_l]
    rfl
  have hI := PowerlessOrdinalInduction.induction_l hℳ φ ζ (PowerlessOmegaOrdinal.ordinal_l hℳ hω)
    (fun c _ h => (hφ c).mpr (by
      intro p f hc
      exact (h₀ p c f hc).2 (fun d hd a g => (hφ d).mp (h d hd) a g)))
  intro p c f hc
  exact (hφ c).mp (hI c (h₀ p c f hc).1) p f hc

theorem accepts_source_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U δ R H : carrier_l ℳ}
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
    (w z V s₁ s₂ s₃ p c f : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω.val) (hz : (z.eval η).val = e.val) (hV : (V.eval η).val = T.val)
    (hs₁ : (s₁.eval η).val = t₁.val) (hs₂ : (s₂.eval η).val = t₂.val) (hs₃ : (s₃.eval η).val = t₃.val)
    (h : (accepts_m w z V s₁ s₂ s₃ p c f).satisfies η) :
    PowerlessTruthSign.sign_l e.val t₁.val H (p.eval η).val (c.eval η).val (f.eval η).val := by
  let q (s : Term ℒ Γ Δ .set) := s.weakenBound SetTheory.SetSort.set
  change ∃ D : type_l U,
    (certificate_m (q w) (q z) (q V) (q s₁) (q s₂) (q s₃) (.bvar .here)).satisfies (η.pushBound D) ∧
    (PowerlessTruthRecord.entry_m (.bvar .here) (q p) (q c) (q f)).satisfies (η.pushBound D) at h
  obtain ⟨D, hD, he⟩ := h
  have h₀ := sound_l hℳ hω ht hT hU hδ hωδ h𝒩 hR hH (η.pushBound D)
    (q w) (q z) (q V) (q s₁) (q s₂) (q s₃) (.bvar .here)
    (by simpa only [q, Term.eval_weakenBound] using hw)
    (by simpa only [q, Term.eval_weakenBound] using hz)
    (by simpa only [q, Term.eval_weakenBound] using hV)
    (by simpa only [q, Term.eval_weakenBound] using hs₁)
    (by simpa only [q, Term.eval_weakenBound] using hs₂)
    (by simpa only [q, Term.eval_weakenBound] using hs₃) hD
  have h₁ := (PowerlessTruthRecordAbsolute.entry_source_l
    (PowerlessStageStructure.transitive_l hℳ hω ht hT hU)
    (η.pushBound D) (.bvar .here) (q p) (q c) (q f)).mp he
  simp only [q, Term.eval_weakenBound] at h₁
  exact h₀ _ _ _ h₁

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthCertificate
