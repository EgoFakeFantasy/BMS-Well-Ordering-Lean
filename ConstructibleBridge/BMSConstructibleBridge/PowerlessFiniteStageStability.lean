import BMSConstructibleBridge.PowerlessFiniteStageSystem
import BMSConstructibleBridge.PowerlessStagePairAbsolute
import BMSConstructibleBridge.PowerlessCoreStageStability

/-!
# 有限核心早层中原稳定公式的解释

六个系统见证及原查询一致正文保持不变。反向由系统成员性实际取回
全部见证；不调用需要小结构完整核心的 stable_formula_l。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteStageStability

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U δ : carrier_l ℳ}
  {hU₀ : ∃ x, member_l ℳ x U} (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val)
  (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
  (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
  (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U)
  (hδ : PowerlessStagePair.limit_l δ)
  (h𝒩 : Theory.Models (structure_l U hU₀) PowerlessFiniteStageHierarchy.theory_m)
  (hωδ : member_l ℳ ω.val δ)

include hℳ hω ht hT hU hδ h𝒩 hωδ


theorem source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w z V s₁ s₂ s₃ n α β : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω.val) (hz : (z.eval η).val = e.val) (hV : (V.eval η).val = T.val)
    (hs₁ : (s₁.eval η).val = t₁.val) (hs₂ : (s₂.eval η).val = t₂.val) (hs₃ : (s₃.eval η).val = t₃.val) :
    (PowerlessStageStability.stable_m w z V s₁ s₂ s₃ n α β).satisfies η ↔
      PowerlessStageStability.stable_l ω.val e.val T.val t₁.val t₂.val t₃.val
        (n.eval η).val (α.eval η).val (β.eval η).val := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  let q (t : Term ℒ Γ Δ .set) :=
    ((((((t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound
      SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound
      SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set)
  let η₀ (A B S R F G : type_l U) :
      Env (structure_l U hU₀) (.set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ :=
    (((((η.pushBound A).pushBound B).pushBound S).pushBound R).pushBound F).pushBound G
  have hA (A B S R F G : type_l U) :
      (PowerlessStageEvaluation.system_m (q w) (q z) (q V) (q s₁) (q s₂) (q s₃)
        (q α) (.bvar (.there (.there (.there (.there (.there .here))))))
        (.bvar (.there (.there (.there .here)))) (.bvar (.there .here))).satisfies (η₀ A B S R F G) ↔
      PowerlessStageEvaluation.system_l ω.val e.val T.val t₁.val t₂.val t₃.val
        (α.eval η).val A.val S.val F.val := by
    have h := PowerlessFiniteStageSystem.source_l hℳ hω ht hT hU hδ h𝒩 hωδ
      (η₀ A B S R F G) (q w) (q z) (q V) (q s₁) (q s₂) (q s₃) (q α)
      (.bvar (.there (.there (.there (.there (.there .here))))))
      (.bvar (.there (.there (.there .here)))) (.bvar (.there .here))
      (by simpa only [q, η₀, Term.eval_weakenBound] using hw)
      (by simpa only [q, η₀, Term.eval_weakenBound] using hz)
      (by simpa only [q, η₀, Term.eval_weakenBound] using hV)
      (by simpa only [q, η₀, Term.eval_weakenBound] using hs₁)
      (by simpa only [q, η₀, Term.eval_weakenBound] using hs₂)
      (by simpa only [q, η₀, Term.eval_weakenBound] using hs₃)
    simp only [q, η₀, Term.eval_weakenBound] at h
    simpa only [q, η₀, Term.eval_weakenBound, Term.eval, Env.pushBound, Assignment.push] using h
  have hB (A B S R F G : type_l U) :
      (PowerlessStageEvaluation.system_m (q w) (q z) (q V) (q s₁) (q s₂) (q s₃)
        (q β) (.bvar (.there (.there (.there (.there .here)))))
        (.bvar (.there (.there .here))) (.bvar .here)).satisfies (η₀ A B S R F G) ↔
      PowerlessStageEvaluation.system_l ω.val e.val T.val t₁.val t₂.val t₃.val
        (β.eval η).val B.val R.val G.val := by
    have h := PowerlessFiniteStageSystem.source_l hℳ hω ht hT hU hδ h𝒩 hωδ
      (η₀ A B S R F G) (q w) (q z) (q V) (q s₁) (q s₂) (q s₃) (q β)
      (.bvar (.there (.there (.there (.there .here)))))
      (.bvar (.there (.there .here))) (.bvar .here)
      (by simpa only [q, η₀, Term.eval_weakenBound] using hw)
      (by simpa only [q, η₀, Term.eval_weakenBound] using hz)
      (by simpa only [q, η₀, Term.eval_weakenBound] using hV)
      (by simpa only [q, η₀, Term.eval_weakenBound] using hs₁)
      (by simpa only [q, η₀, Term.eval_weakenBound] using hs₂)
      (by simpa only [q, η₀, Term.eval_weakenBound] using hs₃)
    simp only [q, η₀, Term.eval_weakenBound] at h
    simpa only [q, η₀, Term.eval_weakenBound, Term.eval, Env.pushBound, Assignment.push] using h
  have hG (A B S R F G : type_l U) :
      (PowerlessLevyAgreement.agreement_m (q w) (q z) (q V) (q s₁) (q s₂) (q s₃)
        (.bvar (.there (.there (.there (.there (.there .here))))))
        (.bvar .here) (.bvar (.there .here)) (q n)).satisfies (η₀ A B S R F G) ↔
      PowerlessLevyAgreement.agreement_l ω.val e.val T.val t₁.val t₂.val t₃.val A.val G.val F.val
        (n.eval η).val := by
    have h := PowerlessLevyAgreement.agreement_formula_l (η₀ A B S R F G)
      (q w) (q z) (q V) (q s₁) (q s₂) (q s₃)
      (.bvar (.there (.there (.there (.there (.there .here)))))) (.bvar .here) (.bvar (.there .here)) (q n)
    simp only [q, η₀, Term.eval_weakenBound] at h
    simp only [Term.eval, Env.pushBound, Assignment.push] at h
    rw [show w.eval η = ω from Subtype.ext hw, show z.eval η = e from Subtype.ext hz,
      show V.eval η = T from Subtype.ext hV, show s₁.eval η = t₁ from Subtype.ext hs₁,
      show s₂.eval η = t₂ from Subtype.ext hs₂, show s₃.eval η = t₃ from Subtype.ext hs₃] at h
    exact h.trans (PowerlessCoreStageStability.agreement_l hℳ hω ht hT hU hδ hωδ)
  have hp := PowerlessStagePairAbsolute.proper_l hℳ hUT η w α β
  rw [hw] at hp
  have hn : (SecondOrderObjectSyntax.member_m n w).satisfies η ↔
      member_l ℳ (n.eval η).val ω.val := by
    change member_l ℳ (n.eval η).val (w.eval η).val ↔ _
    rw [hw]
  simp only [PowerlessStageStability.stable_m, PowerlessStageStability.stable_l, Formula.satisfies]
  apply and_congr hn
  rw [hp]
  apply and_congr_right
  intro hp
  constructor
  · rintro ⟨A, B, S, R, F, G, h₁, h₂, h₃⟩
    exact ⟨A.val, B.val, S.val, R.val, F.val, G.val,
      (hA A B S R F G).mp h₁, (hB A B S R F G).mp h₂, (hG A B S R F G).mp h₃⟩
  · rintro ⟨A, B, S, R, F, G, h₁, h₂, h₃⟩
    have hαδ := (PowerlessStageOrdinal.member_l hℳ hω ht hT hU hp.2.2.1.1).mp (α.eval η).property
    have hβδ := (PowerlessStageOrdinal.member_l hℳ hω ht hT hU hp.2.2.2.1).mp (β.eval η).property
    obtain ⟨hAU, hSU, hFU⟩ := PowerlessFiniteStageSystem.member_l hℳ hω ht hT hU hδ h𝒩 hωδ hαδ h₁
    obtain ⟨hBU, hRU, hGU⟩ := PowerlessFiniteStageSystem.member_l hℳ hω ht hT hU hδ h𝒩 hωδ hβδ h₂
    exact ⟨⟨A, hAU⟩, ⟨B, hBU⟩, ⟨S, hSU⟩, ⟨R, hRU⟩, ⟨F, hFU⟩, ⟨G, hGU⟩,
      (hA ⟨A, hAU⟩ ⟨B, hBU⟩ ⟨S, hSU⟩ ⟨R, hRU⟩ ⟨F, hFU⟩ ⟨G, hGU⟩).mpr h₁,
      (hB ⟨A, hAU⟩ ⟨B, hBU⟩ ⟨S, hSU⟩ ⟨R, hRU⟩ ⟨F, hFU⟩ ⟨G, hGU⟩).mpr h₂,
      (hG ⟨A, hAU⟩ ⟨B, hBU⟩ ⟨S, hSU⟩ ⟨R, hRU⟩ ⟨F, hFU⟩ ⟨G, hGU⟩).mpr h₃⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteStageStability
