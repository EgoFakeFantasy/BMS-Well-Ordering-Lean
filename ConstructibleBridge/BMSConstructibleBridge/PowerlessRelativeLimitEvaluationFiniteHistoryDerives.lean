import BMSConstructibleBridge.PowerlessRelativeLimitEvaluationFiniteHistory
import BMSConstructibleBridge.PowerlessRelativeLimitDeltaSeparationDerives

/-! # 全部内部有限求值历史的原 Z₂ 对象推导

对每个给定参数模式，原句断言全部 n∈ω 都有同层历史 F。实际公式归纳
已覆盖模型内部数域；最后逐 n 用数根码满射接回原商对象，不假设 ω 标准。
这不是无限求值图、规范良序或最终固定高度 BMS 良序句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitEvaluationFiniteHistoryDerives

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def conclusion_m {Γ Δ : SortContext ℒ} (C ω e T A S t₁ t₂ t₃ : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up t)
  membershipLevyBound.boundedForall ω <| .existsE .set <| .conj
    (SecondOrderObjectSyntax.member_m (.bvar .here) (w C))
    (PowerlessEvaluationFiniteHistory.formula_m (w C) (w ω) (w e) (w T) (w A)
      (w t₁) (w t₂) (w t₃) (w S) (.bvar .here) (.bvar (.there .here)))

theorem conclusion_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (C ω e T A S t₁ t₂ t₃ : Term ℒ Γ Δ .set) :
    (conclusion_m C ω e T A S t₁ t₂ t₃).satisfies η ↔
      ∀ n, member_l 𝒩 n (ω.eval η) → ∃ F, member_l 𝒩 F (C.eval η) ∧
        PowerlessEvaluationFiniteHistory.trace_l (C.eval η) (ω.eval η) (e.eval η) (T.eval η) (A.eval η)
          (t₁.eval η) (t₂.eval η) (t₃.eval η) (S.eval η) F n := by
  simp only [conclusion_m, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessEvaluationFiniteHistory.formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m {Δ : SortContext ℒ} (ω e N T A S t₁ t₂ t₃ : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <|
    let B : Term ℒ [.set, .set, .set] Δ .set := .bvar (.there (.there .here))
    let β : Term ℒ [.set, .set, .set] Δ .set := .bvar (.there .here)
    let C : Term ℒ [.set, .set, .set] Δ .set := .bvar .here
    let w (t : Term ℒ [] Δ .set) := up (up (up t))
    .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
      .imp (PowerlessRelativeHierarchySyntax.level_m B β C) <|
        .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
          .imp (parameters_m Δ C (fun v => .fvar v)) <|
            .imp (SecondOrderObjectSyntax.member_m (w S) C) <|
              .imp (SecondOrderOmegaSyntax.omega_m (w ω)) <|
                .imp (SecondOrderObjectSyntax.member_m (w ω) C) <|
                  .imp (.forallE .set (.neg (SecondOrderObjectSyntax.member_m (.bvar .here) (up (w e))))) <|
                    .imp (PowerlessFiniteSequencesSyntax.spec_m (w ω) (w ω) (w N)) <|
                      .imp (SecondOrderObjectSyntax.map_m (w T) (w ω) (w ω)) <|
                        .imp (PowerlessFiniteSequencesSyntax.spec_m (w ω) (w A) (w S)) <|
                          conclusion_m C (w ω) (w e) (w T) (w A) (w S) (w t₁) (w t₂) (w t₃)

def sentence_m {Δ : SortContext ℒ} (ω e N T A S t₁ t₂ t₃ : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m ω e N T A S t₁ t₂ t₃)

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (ω e N T A S t₁ t₂ t₃ : Term ℒ [] Δ .set) :
    (sentence_m ω e N T A S t₁ t₂ t₃).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η B β C hBase hC hLimit hParams hSC hω hωC he hN hT hS
  let ξ := ((η.pushBound B).pushBound β).pushBound C
  have hBase' := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ ξ
    (.bvar (.there (.there .here)))).mp hBase
  have hC' := (PowerlessRelativeHierarchySemantics.level_formula_l K ξ
    (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)).mp hC
  have hLimit' := (PowerlessRelativeHierarchySemantics.limit_formula_l
    (hℳ := hℳ) ξ (.bvar (.there .here))).mp hLimit
  have hParams' : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) C :=
    (parameters_formula_l Δ ξ (.bvar .here) (fun v => .fvar v)).mp hParams
  have hω' := (omega_formula_l ξ (up (up (up ω)))).mp hω
  have hN' := (PowerlessFiniteSequencesSyntax.spec_formula_l ξ _ _ _).mp hN
  have hT' := (map_formula_l ξ _ _ _).mp hT
  have hS' := (PowerlessFiniteSequencesSyntax.spec_formula_l ξ _ _ _).mp hS
  have hSC' : mem_l hℳ ((up (up (up S))).eval ξ) C := hSC
  have hωC' : mem_l hℳ ((up (up (up ω))).eval ξ) C := hωC
  simp only [ξ, up, Term.eval_weakenBound] at hω' hN' hT' hS' hSC' hωC'
  have he' : PowerlessNatural.zero_l (ℳ := SecondOrderQuotient.structure_l hℳ) (e.eval η) := by
    simpa only [PowerlessNatural.zero_l, ThirdOrderSemantics.member_l, Formula.satisfies,
      SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval,
      Env.pushBound_bound_here] using he
  have hωEq := SecondOrderOmega.unique_l hℳ hω' K.omega_spec
  have heEq := SecondOrderQuotient.ext_l hℳ _ _ (fun x =>
    iff_of_false (he' x) (PowerlessBMSQuotientSuccessor.zero_l K x))
  apply (conclusion_formula_l ξ (.bvar .here) (up (up (up ω))) (up (up (up e)))
    (up (up (up T))) (up (up (up A))) (up (up (up S)))
    (up (up (up t₁))) (up (up (up t₂))) (up (up (up t₃)))).mpr
  simp only [ξ, up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here]
  intro n hn
  obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨n, hωEq ▸ hn⟩
  have hi' : (numberCode_l K i).val = n := congrArg Subtype.val hi
  obtain ⟨F, hFC, hF⟩ := PowerlessRelativeLimitEvaluationFiniteHistory.exists_l K
    hBase' hLimit' hC' (hωEq ▸ hωC') η ω e N T A S t₁ t₂ t₃
    hParams' hSC' hωEq heEq hN' hT' hS' i
  exact ⟨F, hFC, hi' ▸ hF⟩

theorem derives_m {Δ : SortContext ℒ} (ω e N T A S t₁ t₂ t₃ : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m ω e N T A S t₁ t₂ t₃)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ ω e N T A S t₁ t₂ t₃)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitEvaluationFiniteHistoryDerives
