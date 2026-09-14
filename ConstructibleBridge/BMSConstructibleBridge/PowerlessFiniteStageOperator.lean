import BMSConstructibleBridge.PowerlessFiniteStageEvaluation
import BMSConstructibleBridge.PowerlessFiniteStageClosure
import BMSConstructibleBridge.PowerlessOperatorFiniteSupport
import BMSConstructibleBridge.PowerlessCoreStageEvaluation
import BMSConstructibleBridge.PowerlessEvaluationFamilyAbsolute

/-!
# 有限核心早层中原求值算子的绝对性与成员性

由固定有限支持取得完整赋值集、求值图和切片闭包，再比较原 operator_m。
原公式的两个存在量词都保留；不存在隐藏的 Core(U) 或新反射前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteStageOperator

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

noncomputable def basis_m : List (Sentence ℒ) :=
  PowerlessFiniteStageEvaluation.basis_m ++
    (PowerlessFiniteStageClosure.basis_m ++ PowerlessOperatorFiniteSupport.support_m.sentences)

def theory_m : Theory ℒ := Theory.ofList basis_m

noncomputable def condition_m {Γ Δ : SortContext ℒ} (A : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  PowerlessRelativizedTheory.instance_m basis_m A

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem core_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) : Theory.Models ℳ theory_m := by
  intro φ hφ
  obtain hφ | hφ := List.mem_append.mp hφ
  · exact PowerlessFiniteStageEvaluation.core_l hℳ φ hφ
  · obtain hφ | hφ := List.mem_append.mp hφ
    · exact PowerlessFiniteStageClosure.core_l hℳ φ hφ
    · exact PowerlessOperatorFiniteSupport.core_l hℳ φ hφ

theorem condition_l {A : carrier_l ℳ} {hA : ∃ x, member_l ℳ x A}
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (a : Term ℒ Γ Δ .set) (h : a.eval η = A) :
    (condition_m a).satisfies η ↔ Theory.Models (structure_l A hA) theory_m :=
  PowerlessRelativizedTheory.instance_l basis_m η a h

theorem evaluation_models_l (hℳ : Theory.Models ℳ theory_m) :
    Theory.Models ℳ PowerlessFiniteStageEvaluation.theory_m :=
  fun φ hφ => hℳ φ (List.mem_append.mpr (Or.inl hφ))

theorem closure_models_l (hℳ : Theory.Models ℳ theory_m) :
    Theory.Models ℳ PowerlessFiniteStageClosure.theory_m :=
  fun φ hφ => hℳ φ (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl hφ))))

theorem operator_models_l (hℳ : Theory.Models ℳ theory_m) :
    Theory.Models ℳ PowerlessOperatorFiniteSupport.theory_m :=
  fun φ hφ => hℳ φ (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr hφ))))

variable {U δ : carrier_l ℳ} {hU₀ : ∃ x, member_l ℳ x U}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val)
  (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
  (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
  (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U)
  (hδ : PowerlessStagePair.limit_l δ)
  (h𝒩 : Theory.Models (structure_l U hU₀) theory_m)

include hℳ hω ht hT hU hδ h𝒩

theorem family_l {w A F S D : type_l U} :
    PowerlessEvaluationFamily.family_l (ℳ := structure_l U hU₀) w A F S D ↔
      PowerlessEvaluationFamily.family_l w.val A.val F.val S.val D.val := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  have hP : ∀ {a b p : carrier_l ℳ}, member_l ℳ a U → member_l ℳ b U →
      ordered_l a b p → member_l ℳ p U :=
    PowerlessStageGraphClosure.ordered_l hℳ hω ht hT hU hδ
  apply PowerlessEvaluationFamilyAbsolute.family_l hUT hP
  intro c f Y hc hf hY
  exact PowerlessFiniteStageClosure.slice_member_l hUT hP (closure_models_l h𝒩) hℳ
    (c := ⟨c, hUT w.val c w.property hc⟩) (f := ⟨f, hUT S.val f S.property hf⟩) hY

variable (hωδ : member_l ℳ ω.val δ)

include hωδ

theorem source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w z V s₁ s₂ s₃ A D : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω.val) (hz : (z.eval η).val = e.val) (hV : (V.eval η).val = T.val)
    (hs₁ : (s₁.eval η).val = t₁.val) (hs₂ : (s₂.eval η).val = t₂.val) (hs₃ : (s₃.eval η).val = t₃.val) :
    (PowerlessEvaluationOperator.operator_m w z V s₁ s₂ s₃ A D).satisfies η ↔
      PowerlessEvaluationOperator.operator_l ω.val e.val T.val t₁.val t₂.val t₃.val
        (A.eval η).val (D.eval η).val := by
  let q (t : Term ℒ Γ Δ .set) :=
    (t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  have ha (S F : type_l U) :
      (PowerlessEvaluationOperator.assignments_m (q w) (q A) (.bvar (.there .here))).satisfies
        ((η.pushBound S).pushBound F) ↔
      PowerlessEvaluationOperator.assignments_l ω.val (A.eval η).val S.val := by
    have h := PowerlessEvaluationOperator.assignments_formula_l ((η.pushBound S).pushBound F)
      (q w) (q A) (.bvar (.there .here))
    simp only [q, Term.eval_weakenBound] at h
    rw [show w.eval η = ω from Subtype.ext hw] at h
    exact h.trans (PowerlessCoreStageEvaluation.assignments_l hℳ hω ht hT hU hωδ hδ)
  have hb (S F : type_l U) :
      (PowerlessEvaluationPresentation.evaluation_m (q w) (q z) (q V) (q A) (q s₁) (q s₂) (q s₃)
        (.bvar (.there .here)) (.bvar .here)).satisfies ((η.pushBound S).pushBound F) ↔
      PowerlessEvaluationRecursion.evaluation_l ω.val e.val T.val (A.eval η).val t₁.val t₂.val t₃.val S.val F.val := by
    have h := PowerlessEvaluationSourceAbsolute.stage_l hℳ hω ht hT hU hωδ hδ
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
      PowerlessEvaluationFamily.family_l ω.val (A.eval η).val F.val S.val (D.eval η).val := by
    have h := PowerlessEvaluationFamily.family_formula_l ((η.pushBound S).pushBound F)
      (q w) (q A) (.bvar .here) (.bvar (.there .here)) (q D)
    simp only [q, Term.eval_weakenBound] at h
    have h₁ := h.trans (family_l hℳ hω ht hT hU hδ h𝒩)
    simpa only [Term.eval, Env.pushBound, Assignment.push, hw] using h₁
  simp only [PowerlessEvaluationOperator.operator_m, Formula.satisfies]
  constructor
  · rintro ⟨S, F, hS, hF, hD⟩
    exact ⟨S.val, F.val, (ha S F).mp hS, (hb S F).mp hF, (hd S F).mp hD⟩
  · rintro ⟨S, F, hS, hF, hD⟩
    have hSU := PowerlessFiniteStageEvaluation.assignments_member_l hℳ hω ht hT hU hωδ hδ
      (evaluation_models_l h𝒩) (A.eval η).property hS
    have hFU := PowerlessFiniteStageEvaluation.evaluation_member_l hℳ hω ht hT hU hωδ hδ
      (evaluation_models_l h𝒩) (A.eval η).property hSU hF
    exact ⟨⟨S, hSU⟩, ⟨F, hFU⟩, (ha ⟨S, hSU⟩ ⟨F, hFU⟩).mpr hS,
      (hb ⟨S, hSU⟩ ⟨F, hFU⟩).mpr hF, (hd ⟨S, hSU⟩ ⟨F, hFU⟩).mpr hD⟩

theorem exists_l (A : type_l U) : ∃ D : type_l U,
    PowerlessEvaluationOperator.operator_l ω.val e.val T.val t₁.val t₂.val t₃.val A.val D.val := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  have hw := (PowerlessSourceOmegaAbsolute.omega_l (hA := hU₀) hℳ hUT hω ω.property ω).mpr rfl
  let η : Env (structure_l U hU₀) [] [.set, .set, .set, .set, .set, .set, .set] :=
    ((((((Env.empty.pushFree A).pushFree t₃).pushFree t₂).pushFree t₁).pushFree T).pushFree e).pushFree ω
  obtain ⟨D, hD⟩ := (PowerlessOperatorFiniteSupport.satisfies_l (operator_models_l h𝒩) η)
    ((omega_formula_l η (.fvar .here)).mpr hw)
  refine ⟨D, ?_⟩
  exact (source_l hℳ hω ht hT hU hδ h𝒩 hωδ (η.pushBound D)
    (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here))))))) (.bvar .here)
    rfl rfl rfl rfl rfl rfl).mp hD

theorem member_l {A D : carrier_l ℳ} (hA : member_l ℳ A U)
    (hD : PowerlessEvaluationOperator.operator_l ω.val e.val T.val t₁.val t₂.val t₃.val A D) :
    member_l ℳ D U := by
  obtain ⟨E, hE⟩ := exists_l hℳ hω ht hT hU hδ h𝒩 hωδ ⟨A, hA⟩
  exact (PowerlessEvaluationOperator.unique_l hℳ hω hE hD) ▸ E.property

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteStageOperator
