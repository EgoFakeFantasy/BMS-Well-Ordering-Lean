import BMSConstructibleBridge.PowerlessTruthCertificate
import BMSConstructibleBridge.PowerlessTruthInduction

/-!
# 低层原公式驱动的真值证书

低层公式使用固定十个自由参数 ω,e,T,t₁,t₂,t₃,n,p,c,f，完全沿用原 AST。
替换由内核 Substitution 完成；不加入语义谓词或全局真值参数。
新记录可以调用低层公式，或者使用原局部规则。低层可靠性仍须证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthOracle

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

abbrev context_m : SortContext ℒ :=
  [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set]

def instance_m (B : Formula ℒ [] context_m) {Γ Δ : SortContext ℒ}
    (ω e T t₁ t₂ t₃ n p c f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  B.substitute (.map (fun {s} (v : Variable ([] : SortContext ℒ) s) => nomatch v)
    (fun {s} (v : Variable context_m s) => match v with
    | .here => ω
    | .there .here => e
    | .there (.there .here) => T
    | .there (.there (.there .here)) => t₁
    | .there (.there (.there (.there .here))) => t₂
    | .there (.there (.there (.there (.there .here)))) => t₃
    | .there (.there (.there (.there (.there (.there .here))))) => n
    | .there (.there (.there (.there (.there (.there (.there .here)))))) => p
    | .there (.there (.there (.there (.there (.there (.there (.there .here))))))) => c
    | .there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) => f))

def env_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e T t₁ t₂ t₃ n p c f : carrier_l ℳ) : Env ℳ [] context_m :=
  (((((((((Env.empty.pushFree f).pushFree c).pushFree p).pushFree n).pushFree t₃).pushFree t₂
    ).pushFree t₁).pushFree T).pushFree e).pushFree ω

theorem instance_formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (B : Formula ℒ [] context_m) {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ)
    (ω e T t₁ t₂ t₃ n p c f : Term ℒ Γ Δ .set) :
    (instance_m B ω e T t₁ t₂ t₃ n p c f).satisfies η ↔
      B.satisfies (env_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η)
        (t₃.eval η) (n.eval η) (p.eval η) (c.eval η) (f.eval η)) := by
  rw [instance_m, Formula.satisfies_substitute]
  apply Iff.of_eq
  congr 1
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    repeat' first | rfl | cases ‹Variable _ _›

def certificate_m (B : Formula ℒ [] context_m) {Γ Δ : SortContext ℒ}
    (ω e T t₁ t₂ t₃ n D : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let q (s : Term ℒ Γ Δ .set) := (((s.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
    ).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .forallE .set (.imp
    (SecondOrderObjectSyntax.member_m (.bvar .here) (D.weakenBound SetTheory.SetSort.set))
    (.existsE .set (.existsE .set (.existsE .set (.conj
      (PowerlessTruthRecord.record_m (.bvar (.there (.there .here))) (.bvar (.there .here))
        (.bvar .here) (.bvar (.there (.there (.there .here)))))
      (.conj (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (q ω))
        (.disj
          (instance_m B (q ω) (q e) (q T) (q t₁) (q t₂) (q t₃) (q n)
            (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))
          (PowerlessTruthStep.step_m (q ω) (q e) (q T) (q t₁) (q t₂) (q t₃) (q D)
            (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)))))))))

def accepts_m (B : Formula ℒ [] context_m) {Γ Δ : SortContext ℒ}
    (ω e T t₁ t₂ t₃ n p c f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let q (s : Term ℒ Γ Δ .set) := s.weakenBound SetTheory.SetSort.set
  .existsE .set (.conj (certificate_m B (q ω) (q e) (q T) (q t₁) (q t₂) (q t₃) (q n) (.bvar .here))
    (PowerlessTruthRecord.entry_m (.bvar .here) (q p) (q c) (q f)))

theorem sound_l (B : Formula ℒ [] context_m) {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U δ R H : carrier_l ℳ}
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
    (w z V s₁ s₂ s₃ n D : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω.val) (hz : (z.eval η).val = e.val) (hV : (V.eval η).val = T.val)
    (hs₁ : (s₁.eval η).val = t₁.val) (hs₂ : (s₂.eval η).val = t₂.val) (hs₃ : (s₃.eval η).val = t₃.val)
    (hB : ∀ p c f : type_l U,
      B.satisfies (env_l (w.eval η) (z.eval η) (V.eval η) (s₁.eval η) (s₂.eval η)
        (s₃.eval η) (n.eval η) p c f) →
          PowerlessTruthSign.sign_l e.val t₁.val H p.val c.val f.val)
    (hD : (certificate_m B w z V s₁ s₂ s₃ n D).satisfies η) :
    PowerlessTruthSign.valid_l e.val t₁.val H (D.eval η).val := by
  let q (s : Term ℒ Γ Δ .set) := (((s.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
    ).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  change ∀ r : type_l U,
    member_l (structure_l U hU₀) r ((D.weakenBound SetTheory.SetSort.set).eval (η.pushBound r)) →
    ∃ p c f : type_l U, PowerlessTruthRecord.record_l (ℳ := structure_l U hU₀) p c f r ∧
      member_l (structure_l U hU₀) c ((q w).eval ((((η.pushBound r).pushBound p).pushBound c).pushBound f)) ∧
      ((instance_m B (q w) (q z) (q V) (q s₁) (q s₂) (q s₃) (q n)
        (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)).satisfies
          ((((η.pushBound r).pushBound p).pushBound c).pushBound f) ∨
      (PowerlessTruthStep.step_m (q w) (q z) (q V) (q s₁) (q s₂) (q s₃) (q D)
        (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)).satisfies
          ((((η.pushBound r).pushBound p).pushBound c).pushBound f)) at hD
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
    rcases h₂ with h₂ | h₂
    · apply hB p₀ c₀ f₀
      have h₂ := (instance_formula_l B
        ((((η.pushBound r₀).pushBound p₀).pushBound c₀).pushBound f₀)
        (q w) (q z) (q V) (q s₁) (q s₂) (q s₃) (q n)
        (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)).mp h₂
      simp only [q, Term.eval_weakenBound] at h₂
      simpa only [Term.eval, Env.pushBound, Assignment.push] using h₂
    · have h₄ := PowerlessTruthStep.source_l hℳ hω ht hT hU hδ hωδ h𝒩 hR hH
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
  exact PowerlessTruthInduction.sound_l hℳ hω h₀

theorem accepts_source_l (B : Formula ℒ [] context_m) {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U δ R H : carrier_l ℳ}
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
    (w z V s₁ s₂ s₃ n p c f : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω.val) (hz : (z.eval η).val = e.val) (hV : (V.eval η).val = T.val)
    (hs₁ : (s₁.eval η).val = t₁.val) (hs₂ : (s₂.eval η).val = t₂.val) (hs₃ : (s₃.eval η).val = t₃.val)
    (hB : ∀ p c f : type_l U,
      B.satisfies (env_l (w.eval η) (z.eval η) (V.eval η) (s₁.eval η) (s₂.eval η)
        (s₃.eval η) (n.eval η) p c f) →
          PowerlessTruthSign.sign_l e.val t₁.val H p.val c.val f.val)
    (h : (accepts_m B w z V s₁ s₂ s₃ n p c f).satisfies η) :
    PowerlessTruthSign.sign_l e.val t₁.val H (p.eval η).val (c.eval η).val (f.eval η).val := by
  let q (s : Term ℒ Γ Δ .set) := s.weakenBound SetTheory.SetSort.set
  change ∃ D : type_l U,
    (certificate_m B (q w) (q z) (q V) (q s₁) (q s₂) (q s₃) (q n) (.bvar .here)).satisfies (η.pushBound D) ∧
    (PowerlessTruthRecord.entry_m (.bvar .here) (q p) (q c) (q f)).satisfies (η.pushBound D) at h
  obtain ⟨D, hD, he⟩ := h
  have h₀ := sound_l B hℳ hω ht hT hU hδ hωδ h𝒩 hR hH (η.pushBound D)
    (q w) (q z) (q V) (q s₁) (q s₂) (q s₃) (q n) (.bvar .here)
    (by simpa only [q, Term.eval_weakenBound] using hw)
    (by simpa only [q, Term.eval_weakenBound] using hz)
    (by simpa only [q, Term.eval_weakenBound] using hV)
    (by simpa only [q, Term.eval_weakenBound] using hs₁)
    (by simpa only [q, Term.eval_weakenBound] using hs₂)
    (by simpa only [q, Term.eval_weakenBound] using hs₃)
    (fun p c f h => hB p c f (by simpa only [q, Term.eval_weakenBound] using h)) hD
  have h₁ := (PowerlessTruthRecordAbsolute.entry_source_l
    (PowerlessStageStructure.transitive_l hℳ hω ht hT hU)
    (η.pushBound D) (.bvar .here) (q p) (q c) (q f)).mp he
  simp only [q, Term.eval_weakenBound] at h₁
  exact h₀ _ _ _ h₁

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthOracle
