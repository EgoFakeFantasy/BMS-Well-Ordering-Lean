import BMSConstructibleBridge.PowerlessAssignmentsFiniteSupport
import BMSConstructibleBridge.PowerlessEvaluationFiniteSupport
import BMSConstructibleBridge.PowerlessRelativizedTheory
import BMSConstructibleBridge.PowerlessAssignmentsAbsolute
import BMSConstructibleBridge.PowerlessEvaluationSourceAbsolute
import BMSConstructibleBridge.PowerlessSourceOmegaAbsolute

/-!
# 实际早层中求值见证的有限核心条件

两个经原 Hilbert 推导抽出的有限列表组成同一个固定片段。
该片段实际保证完整赋值集和整个原求值图落在早层中，不再要求层内完整核心。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteStageEvaluation

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

noncomputable def basis_m : List (Sentence ℒ) := PowerlessAssignmentsFiniteSupport.support_m.sentences ++
  PowerlessEvaluationFiniteSupport.support_m.sentences

def theory_m : Theory ℒ := Theory.ofList basis_m

noncomputable def condition_m {Γ Δ : SortContext ℒ} (A : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  PowerlessRelativizedTheory.instance_m basis_m A

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem core_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) : Theory.Models ℳ theory_m := by
  intro φ hφ
  obtain hφ | hφ := List.mem_append.mp hφ
  · exact hℳ φ (PowerlessAssignmentsFiniteSupport.support_m.subset φ hφ)
  · exact hℳ φ (PowerlessEvaluationFiniteSupport.support_m.subset φ hφ)

theorem condition_l {A : carrier_l ℳ} {hA : ∃ x, member_l ℳ x A}
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (a : Term ℒ Γ Δ .set) (h : a.eval η = A) :
    (condition_m a).satisfies η ↔ Theory.Models (structure_l A hA) theory_m :=
  PowerlessRelativizedTheory.instance_l basis_m η a h

variable {U δ : carrier_l ℳ} {hU₀ : ∃ x, member_l ℳ x U}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val)
  (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
  (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
  (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U)
  (hωδ : member_l ℳ ω.val δ) (hδ : PowerlessStagePair.limit_l δ)
  (h𝒩 : Theory.Models (structure_l U hU₀) theory_m)

include hℳ hω ht hT hU hωδ hδ h𝒩

theorem assignments_exists_l (A : type_l U) : ∃ S : type_l U,
    PowerlessEvaluationOperator.assignments_l ω.val A.val S.val := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  have hw := (PowerlessSourceOmegaAbsolute.omega_l (hA := hU₀) hℳ hUT hω ω.property ω).mpr rfl
  have h₀ : Theory.Models (structure_l U hU₀) PowerlessAssignmentsFiniteSupport.theory_m :=
    fun φ hφ => h𝒩 φ (List.mem_append.mpr (Or.inl hφ))
  obtain ⟨S, hS⟩ := PowerlessAssignmentsFiniteSupport.exists_l h₀ hw A
  obtain ⟨_, w, hw₀, h⟩ := PowerlessAssignmentsAbsolute.stage_l hℳ hω ht hT hU hωδ hδ
  rw [show w = ω from Subtype.ext hw₀] at h
  exact ⟨S, (h A S).mp hS⟩

theorem assignments_member_l {A S : carrier_l ℳ} (hA : member_l ℳ A U)
    (hS : PowerlessEvaluationOperator.assignments_l ω.val A S) : member_l ℳ S U := by
  obtain ⟨R, hR⟩ := assignments_exists_l hℳ hω ht hT hU hωδ hδ h𝒩 ⟨A, hA⟩
  have h : R.val = S := (PowerlessTheory.ext_l hℳ).eq_of_same_members R.val S
    (fun f => (hR f).trans (hS f).symm)
  exact h ▸ R.property

theorem evaluation_exists_l (A S : type_l U) : ∃ F : type_l U,
    PowerlessEvaluationRecursion.evaluation_l ω.val e.val T.val A.val t₁.val t₂.val t₃.val S.val F.val := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  have hw := (PowerlessSourceOmegaAbsolute.omega_l (hA := hU₀) hℳ hUT hω ω.property ω).mpr rfl
  have h₀ : Theory.Models (structure_l U hU₀) PowerlessEvaluationFiniteSupport.theory_m :=
    fun φ hφ => h𝒩 φ (List.mem_append.mpr (Or.inr hφ))
  let η : Env (structure_l U hU₀) [] [.set, .set, .set, .set, .set, .set, .set, .set] :=
    (((((((Env.empty.pushFree S).pushFree t₃).pushFree t₂).pushFree t₁).pushFree A).pushFree T).pushFree e).pushFree ω
  obtain ⟨F, hF⟩ := (PowerlessEvaluationFiniteSupport.satisfies_l h₀ η)
    ((omega_formula_l η (.fvar .here)).mpr hw)
  refine ⟨F, ?_⟩
  exact (PowerlessEvaluationSourceAbsolute.stage_l hℳ hω ht hT hU hωδ hδ (η.pushBound F)
    (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.bvar .here)
    rfl rfl rfl rfl rfl rfl).mp hF

theorem evaluation_member_l {A S F : carrier_l ℳ} (hA : member_l ℳ A U) (hS : member_l ℳ S U)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω.val e.val T.val A t₁.val t₂.val t₃.val S F) : member_l ℳ F U := by
  obtain ⟨G, hG⟩ := evaluation_exists_l hℳ hω ht hT hU hωδ hδ h𝒩 ⟨A, hA⟩ ⟨S, hS⟩
  obtain ⟨H, _, h⟩ := PowerlessEvaluationRecursion.exists_unique_l hℳ hω e.val T.val A t₁.val t₂.val t₃.val S
  exact (h G.val hG).trans (h F hF).symm ▸ G.property

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteStageEvaluation
