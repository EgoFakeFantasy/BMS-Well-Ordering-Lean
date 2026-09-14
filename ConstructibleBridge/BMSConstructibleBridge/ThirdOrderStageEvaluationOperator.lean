import BMSConstructibleBridge.ThirdOrderStageEvaluationFamily
import BMSConstructibleBridge.ThirdOrderStageEvaluationMember
import BMSConstructibleBridge.PowerlessAssignmentsAbsolute

/-!
# 原求值子集算子在 Cκ 中的闭包和公式绝对性

原 operator_m 及其全部存在量词不变。赋值集合和整个求值图先实际落级，
再使用原公式正确性；不把成员结构假定为新的无幂集模型。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStageEvaluationOperator

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
  {ω e T t₁ t₂ t₃ κ U : carrier_l ℳ} (hω : omega_l ω) (hκ : ThirdOrderOmegaOne.first_l ω κ)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
  (hU : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ κ U)

include hℳ hω hκ ht hT hU

theorem member_l {A D : carrier_l ℳ} (hA : ThirdOrderSemantics.member_l ℳ A U)
    (hD : PowerlessEvaluationOperator.operator_l ω e T t₁ t₂ t₃ A D) : ThirdOrderSemantics.member_l ℳ D U := by
  obtain ⟨S, F, hS, hF, hD⟩ := hD
  have hSU := ThirdOrderStageEvaluationClosure.assignments_l hℳ hω hκ ht hT hU hA hS
  have hFU := ThirdOrderStageEvaluationMember.member_l hℳ hω hκ ht hT hU hA hSU hF
  exact ThirdOrderStageEvaluationFamily.member_l hℳ hω hκ ht hT hU hA hFU hSU hD

theorem exists_l {A : carrier_l ℳ} (hA : ThirdOrderSemantics.member_l ℳ A U) :
    ∃ D, PowerlessEvaluationOperator.operator_l ω e T t₁ t₂ t₃ A D ∧ ThirdOrderSemantics.member_l ℳ D U := by
  obtain ⟨D, hD⟩ := PowerlessEvaluationOperator.exists_l (ThirdOrderTheory.core_l hℳ) hω e T t₁ t₂ t₃ A
  exact ⟨D, hD, member_l hℳ hω hκ ht hT hU hA hD⟩

theorem source_l {hU₀ : ∃ x, ThirdOrderSemantics.member_l ℳ x U}
    {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w z V s₁ s₂ s₃ A D : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω) (hz : (z.eval η).val = e) (hV : (V.eval η).val = T)
    (hs₁ : (s₁.eval η).val = t₁) (hs₂ : (s₂.eval η).val = t₂) (hs₃ : (s₃.eval η).val = t₃) :
    (PowerlessEvaluationOperator.operator_m w z V s₁ s₂ s₃ A D).satisfies η ↔
      PowerlessEvaluationOperator.operator_l ω e T t₁ t₂ t₃ (A.eval η).val (D.eval η).val := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  have hUT := PowerlessStageStructure.transitive_l h₀ hω ht hT hU
  have hκ₀ := ThirdOrderStageLimit.limit_l h₀ hω hκ
  have hωκ := ThirdOrderCountableSuccessor.omega_mem_l h₀ hω hκ
  have hG : ∀ n, ThirdOrderSemantics.member_l ℳ n (w.eval η).val → ∀ f,
      map_l f n (A.eval η).val → ThirdOrderSemantics.member_l ℳ f U := by
    intro n hn f hf
    apply PowerlessStageFiniteGraphs.finite_l h₀ hω ht hT hU hκ₀
      (fun x hx => PowerlessOrdinal.transitive_l hκ.1 ω x hωκ hx) n (by simpa only [hw] using hn) f
    exact PowerlessFunction.range_l h₀ hf
      (fun x y hxy => hUT (A.eval η).val y (A.eval η).property (PowerlessFunction.value_mem_l h₀ hf hxy).2)
  let q (t : Term ℒ Γ Δ .set) :=
    (t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  have ha (S F : type_l U) :
      (PowerlessEvaluationOperator.assignments_m (q w) (q A) (.bvar (.there .here))).satisfies
        ((η.pushBound S).pushBound F) ↔
      PowerlessEvaluationOperator.assignments_l ω (A.eval η).val S.val := by
    have h := PowerlessEvaluationOperator.assignments_formula_l ((η.pushBound S).pushBound F)
      (q w) (q A) (.bvar (.there .here))
    simp only [q, Term.eval_weakenBound] at h
    have h₁ := h.trans (PowerlessAssignmentsAbsolute.assignments_l
      (hB := hU₀) (ω := w.eval η) (A := A.eval η) (S := S) hUT hG)
    simpa only [hw] using h₁
  have hb (S F : type_l U) :
      (PowerlessEvaluationPresentation.evaluation_m (q w) (q z) (q V) (q A) (q s₁) (q s₂) (q s₃)
        (.bvar (.there .here)) (.bvar .here)).satisfies ((η.pushBound S).pushBound F) ↔
      PowerlessEvaluationRecursion.evaluation_l ω e T (A.eval η).val t₁ t₂ t₃ S.val F.val := by
    have h := PowerlessEvaluationSourceAbsolute.stage_l h₀ hω ht hT hU hωκ hκ₀
      ((η.pushBound S).pushBound F) (q w) (q z) (q V) (q A) (q s₁) (q s₂) (q s₃)
      (.bvar (.there .here)) (.bvar .here)
      (by simpa only [q, Term.eval_weakenBound] using hw)
      (by simpa only [q, Term.eval_weakenBound] using hz)
      (by simpa only [q, Term.eval_weakenBound] using hV)
      (by simpa only [q, Term.eval_weakenBound] using hs₁)
      (by simpa only [q, Term.eval_weakenBound] using hs₂)
      (by simpa only [q, Term.eval_weakenBound] using hs₃)
    simp only [q, Term.eval_weakenBound] at h
    simpa only [Term.eval, Env.pushBound, Assignment.push] using h
  have hd (S F : type_l U) :
      (PowerlessEvaluationFamily.family_m (q w) (q A) (.bvar .here) (.bvar (.there .here)) (q D)).satisfies
        ((η.pushBound S).pushBound F) ↔
      PowerlessEvaluationFamily.family_l ω (A.eval η).val F.val S.val (D.eval η).val := by
    have h := ThirdOrderStageEvaluationFamily.source_l hℳ hω hκ ht hT hU
      ((η.pushBound S).pushBound F) (q w) (q A) (.bvar .here) (.bvar (.there .here)) (q D)
      (by simpa only [q, Term.eval_weakenBound] using hw)
    simp only [q, Term.eval_weakenBound] at h
    simpa only [Term.eval, Env.pushBound, Assignment.push] using h
  simp only [PowerlessEvaluationOperator.operator_m, Formula.satisfies]
  constructor
  · rintro ⟨S, F, hS, hF, hD⟩
    exact ⟨S.val, F.val, (ha S F).mp hS, (hb S F).mp hF, (hd S F).mp hD⟩
  · rintro ⟨S, F, hS, hF, hD⟩
    have hSU := ThirdOrderStageEvaluationClosure.assignments_l hℳ hω hκ ht hT hU (A.eval η).property hS
    have hFU := ThirdOrderStageEvaluationMember.member_l hℳ hω hκ ht hT hU (A.eval η).property hSU hF
    exact ⟨⟨S, hSU⟩, ⟨F, hFU⟩, (ha ⟨S, hSU⟩ ⟨F, hFU⟩).mpr hS,
      (hb ⟨S, hSU⟩ ⟨F, hFU⟩).mpr hF, (hd ⟨S, hSU⟩ ⟨F, hFU⟩).mpr hD⟩

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStageEvaluationOperator
