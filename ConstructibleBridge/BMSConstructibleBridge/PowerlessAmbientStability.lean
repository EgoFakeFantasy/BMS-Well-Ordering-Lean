import BMSConstructibleBridge.PowerlessAmbientAgreement
import BMSConstructibleBridge.PowerlessFiniteStageStability

/-!
# 具名下层到当前求值层的原稳定公式

公式没有上端点或上端点完整求值图参数。三个存在见证仅为下层
及其赋值集、求值图；当前层真值由固定外部层号的原部分真值读取。
在具有指定有限支持的实际层中，精确解释原 stable_l 到该层端点。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessAmbientStability

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

def stable_m (k : Nat) {Γ Δ : SortContext ℒ}
    (ω e T t₁ t₂ t₃ n α : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let q (t : Term ℒ Γ Δ .set) :=
    ((t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .conj (SecondOrderObjectSyntax.member_m n ω)
    (.conj (SecondOrderObjectSyntax.member_m ω α) (.conj (PowerlessStagePair.limit_m α)
      (.existsE .set (.existsE .set (.existsE .set (.conj
        (PowerlessStageEvaluation.system_m (q ω) (q e) (q T) (q t₁) (q t₂) (q t₃) (q α)
          (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))
        (PowerlessAmbientAgreement.agreement_m k (q ω) (q e) (q T) (q t₁) (q t₂) (q t₃) (q n)
          (.bvar (.there (.there .here))) (.bvar .here))))))))

theorem source_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {U δ R H : carrier_l ℳ} {hU₀ : ∃ x, member_l ℳ x U}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val)
    (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
    (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
    (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U)
    (hδ : PowerlessStagePair.limit_l δ) (hωδ : member_l ℳ ω.val δ)
    (h𝒩 : Theory.Models (structure_l U hU₀) PowerlessFiniteStageHierarchy.theory_m)
    (h₀ : Theory.Models (structure_l U hU₀) PowerlessTruthIntroduction.theory_m)
    (hR : PowerlessEvaluationOperator.assignments_l ω.val U R)
    (hH : PowerlessEvaluationRecursion.evaluation_l ω.val e.val T.val U t₁.val t₂.val t₃.val R H)
    (k : Nat)
    (hS : ∀ j, j < k → Theory.Models (structure_l U hU₀)
      (PowerlessOracleIntroduction.theory_m
        (PowerlessPartialTruthIntroduction.oracle_m (PowerlessPartialTruth.formula_m j))))
    {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w z V s₁ s₂ s₃ n α : Term ℒ Γ Δ .set)
    (hw : w.eval η = ω) (hz : z.eval η = e) (hV : V.eval η = T)
    (hs₁ : s₁.eval η = t₁) (hs₂ : s₂.eval η = t₂) (hs₃ : s₃.eval η = t₃)
    (hn : PowerlessNumeral.numeral_l e.val k (n.eval η).val) :
    (stable_m k w z V s₁ s₂ s₃ n α).satisfies η ↔
      PowerlessStageStability.stable_l ω.val e.val T.val t₁.val t₂.val t₃.val (n.eval η).val (α.eval η).val δ := by
  let q (t : Term ℒ Γ Δ .set) :=
    ((t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  let η₀ (A S F : type_l U) : Env (structure_l U hU₀) (.set :: .set :: .set :: Γ) Δ :=
    ((η.pushBound A).pushBound S).pushBound F
  have hA (A S F : type_l U) :
      (PowerlessStageEvaluation.system_m (q w) (q z) (q V) (q s₁) (q s₂) (q s₃) (q α)
        (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)).satisfies (η₀ A S F) ↔
      PowerlessStageEvaluation.system_l ω.val e.val T.val t₁.val t₂.val t₃.val (α.eval η).val A.val S.val F.val := by
    have h := PowerlessFiniteStageSystem.source_l hℳ hω ht hT hU hδ h𝒩 hωδ
      (η₀ A S F) (q w) (q z) (q V) (q s₁) (q s₂) (q s₃) (q α)
      (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)
      (by simp only [q, η₀, Term.eval_weakenBound, hw])
      (by simp only [q, η₀, Term.eval_weakenBound, hz])
      (by simp only [q, η₀, Term.eval_weakenBound, hV])
      (by simp only [q, η₀, Term.eval_weakenBound, hs₁])
      (by simp only [q, η₀, Term.eval_weakenBound, hs₂])
      (by simp only [q, η₀, Term.eval_weakenBound, hs₃])
    simp only [q, η₀, Term.eval_weakenBound] at h
    simpa only [q, η₀, Term.eval, Env.pushBound, Assignment.push] using h
  have hG (A S F : type_l U) :
      (PowerlessAmbientAgreement.agreement_m k (q w) (q z) (q V) (q s₁) (q s₂) (q s₃) (q n)
        (.bvar (.there (.there .here))) (.bvar .here)).satisfies (η₀ A S F) ↔
      PowerlessLevyAgreement.agreement_l ω.val e.val T.val t₁.val t₂.val t₃.val A.val F.val H (n.eval η).val := by
    have h := PowerlessAmbientAgreement.agreement_formula_l k (η₀ A S F)
      (q w) (q z) (q V) (q s₁) (q s₂) (q s₃) (q n)
      (.bvar (.there (.there .here))) (.bvar .here)
    simp only [q, η₀, Term.eval_weakenBound] at h
    simp only [Term.eval, Env.pushBound, Assignment.push] at h
    rw [hw, hz, hV, hs₁, hs₂, hs₃] at h
    exact h.trans (PowerlessAmbientAgreement.absolute_l hℳ hω ht hT hU hδ hωδ
      (PowerlessFiniteStageOperator.evaluation_models_l (PowerlessFiniteStageHierarchy.operator_models_l h𝒩))
      h₀ hR hH k hn hS)
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  have hN : (SecondOrderObjectSyntax.member_m n w).satisfies η ↔ member_l ℳ (n.eval η).val ω.val := by
    change member_l ℳ (n.eval η).val (w.eval η).val ↔ _
    rw [hw]
  have hW : (SecondOrderObjectSyntax.member_m w α).satisfies η ↔ member_l ℳ ω.val (α.eval η).val := by
    change member_l ℳ (w.eval η).val (α.eval η).val ↔ _
    rw [hw]
  simp only [stable_m, Formula.satisfies]
  rw [hN, hW, PowerlessStagePairAbsolute.limit_l hℳ hUT η α]
  constructor
  · rintro ⟨hnω, hωα, hα, A, S, F, h₁, h₂⟩
    have hαδ := (PowerlessStageOrdinal.member_l hℳ hω ht hT hU hα.1).mp (α.eval η).property
    have h₃ := (hG A S F).mp h₂
    exact ⟨hnω, ⟨hωα, hαδ, hα, hδ⟩, A.val, U, S.val, R, F.val, H,
      (hA A S F).mp h₁, ⟨hU, hR, hH⟩, fun c p hc f hf => (h₃ c p hc f hf).symm⟩
  · intro h
    obtain ⟨A, S, F, h₁⟩ := PowerlessStageEvaluation.exists_l hℳ hω h.2.1.2.2.1.1 e.val T.val t₁.val t₂.val t₃.val
    have h₂ := ((PowerlessStageStability.compare_l hℳ hω h₁ ⟨hU, hR, hH⟩).mp h).2.2
    obtain ⟨hAU, hSU, hFU⟩ := PowerlessFiniteStageSystem.member_l hℳ hω ht hT hU hδ h𝒩 hωδ h.2.1.2.1 h₁
    refine ⟨h.1, h.2.1.1, h.2.1.2.2.1, ⟨A, hAU⟩, ⟨S, hSU⟩, ⟨F, hFU⟩,
      (hA ⟨A, hAU⟩ ⟨S, hSU⟩ ⟨F, hFU⟩).mpr h₁, ?_⟩
    exact (hG ⟨A, hAU⟩ ⟨S, hSU⟩ ⟨F, hFU⟩).mpr (fun c p hc f hf => (h₂ c p hc f hf).symm)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessAmbientStability
