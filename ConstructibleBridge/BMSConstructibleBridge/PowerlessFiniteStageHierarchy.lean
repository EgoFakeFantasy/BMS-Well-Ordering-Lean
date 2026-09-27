import BMSConstructibleBridge.PowerlessFiniteHierarchySource
import BMSConstructibleBridge.PowerlessHierarchyFiniteSupport
import BMSConstructibleBridge.PowerlessOrdinalBounded

/-!
# 有限核心早层中的完整层次图存在与成员性

将原层次存在闭句的有限支持并入已有算子片段。
内部源见证经原公式绝对性变成实际环境层次图，再由环境唯一性识别原图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteStageHierarchy

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

noncomputable def basis_m : List (Sentence ℒ) :=
  PowerlessFiniteStageOperator.basis_m ++ PowerlessHierarchyFiniteSupport.support_m.sentences

def theory_m : Theory ℒ := Theory.ofList basis_m

noncomputable def condition_m {Γ Δ : SortContext ℒ} (A : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  PowerlessRelativizedTheory.instance_m basis_m A

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem core_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) : Theory.Models ℳ theory_m := by
  intro φ hφ
  obtain hφ | hφ := List.mem_append.mp hφ
  · exact PowerlessFiniteStageOperator.core_l hℳ φ hφ
  · exact PowerlessHierarchyFiniteSupport.core_l hℳ φ hφ

theorem condition_l {A : carrier_l ℳ} {hA : ∃ x, member_l ℳ x A}
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (a : Term ℒ Γ Δ .set) (h : a.eval η = A) :
    (condition_m a).satisfies η ↔ Theory.Models (structure_l A hA) theory_m :=
  PowerlessRelativizedTheory.instance_l basis_m η a h

theorem operator_models_l (hℳ : Theory.Models ℳ theory_m) :
    Theory.Models ℳ PowerlessFiniteStageOperator.theory_m :=
  fun φ hφ => hℳ φ (List.mem_append.mpr (Or.inl hφ))

theorem hierarchy_models_l (hℳ : Theory.Models ℳ theory_m) :
    Theory.Models ℳ PowerlessHierarchyFiniteSupport.theory_m :=
  fun φ hφ => hℳ φ (List.mem_append.mpr (Or.inr hφ))

variable {U δ : carrier_l ℳ} {hU₀ : ∃ x, member_l ℳ x U}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val)
  (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
  (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
  (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U)
  (hδ : PowerlessStagePair.limit_l δ)
  (h𝒩 : Theory.Models (structure_l U hU₀) theory_m)
  (hωδ : member_l ℳ ω.val δ)

include hℳ hω ht hT hU hδ h𝒩 hωδ

theorem exists_l (α : type_l U) (hα : PowerlessOrdinal.ordinal_l α.val) :
    ∃ f : type_l U, PowerlessEvaluationHierarchy.hierarchy_l
      ω.val e.val T.val t₁.val t₂.val t₃.val f.val α.val := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  have hw := (PowerlessSourceOmegaAbsolute.omega_l (hA := hU₀) hℳ hUT hω ω.property ω).mpr rfl
  let η : Env (structure_l U hU₀) [] [.set, .set, .set, .set, .set, .set, .set] :=
    ((((((Env.empty.pushFree α).pushFree t₃).pushFree t₂).pushFree t₁).pushFree T).pushFree e).pushFree ω
  have hα₀ := (PowerlessOrdinalBounded.source_l hℳ hUT η
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))).mpr hα
  obtain ⟨f, hf⟩ := (PowerlessHierarchyFiniteSupport.satisfies_l (hierarchy_models_l h𝒩) η)
    ((omega_formula_l η (.fvar .here)).mpr hw) hα₀
  refine ⟨f, ?_⟩
  exact (PowerlessFiniteHierarchySource.source_l hℳ hω ht hT hU hδ (operator_models_l h𝒩) hωδ
    (η.pushBound f) (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.bvar .here) (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
    rfl rfl rfl rfl rfl rfl).mp hf

theorem member_l {α f : carrier_l ℳ} (hα : PowerlessOrdinal.ordinal_l α) (hαU : member_l ℳ α U)
    (hf : PowerlessEvaluationHierarchy.hierarchy_l ω.val e.val T.val t₁.val t₂.val t₃.val f α) :
    member_l ℳ f U := by
  obtain ⟨g, hg⟩ := exists_l hℳ hω ht hT hU hδ h𝒩 hωδ ⟨α, hαU⟩ hα
  obtain ⟨F, _, h⟩ := PowerlessEvaluationHierarchy.exists_unique_l hℳ hω hα e.val T.val t₁.val t₂.val t₃.val
  exact (h g.val hg).trans (h f hf).symm ▸ g.property

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteStageHierarchy

