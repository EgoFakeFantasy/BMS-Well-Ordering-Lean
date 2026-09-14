import BMSConstructibleBridge.PowerlessAmbientAssignments
import BMSConstructibleBridge.PowerlessStageFiniteGraphs
import BMSConstructibleBridge.PowerlessValueAbsolute

/-!
# 极限当前层中的实际有限赋值与合法变量槽

同一赋值图属于某个更早的传递层，其所有图值也在该层。
因此内部量化的值域足以表达当前层的有限赋值，不需要小层的完整核心。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageAmbientAssignments

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

include hℳ hω ht hT hU hδ

theorem range_l {f : type_l U} {n : carrier_l ℳ} (hf : map_l f.val n U) :
    ∃ A : type_l U, map_l f.val n A.val := by
  obtain ⟨β, A, hβ, hA, hfA⟩ :=
    (PowerlessStageStructure.limit_l hℳ hω hU hδ.2.2 f.val).mp f.property
  have hAT := PowerlessStageStructure.transitive_l hℳ hω ht hT hA
  exact ⟨⟨A, PowerlessStageStructure.member_l hℳ hω ht hT hA hU hβ⟩,
    PowerlessFunction.range_l hℳ hf
      (fun _ _ hxy => (PowerlessValueAbsolute.coordinates_l hAT hfA hxy).2)⟩

theorem finite_l {f : type_l U} :
    PowerlessAmbientAssignments.finite_l (ℳ := structure_l U hU₀) ω f ↔
      ∃ n, member_l ℳ n ω.val ∧ map_l f.val n U := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  constructor
  · rintro ⟨n, A, hn, hf⟩
    have hf₀ := (PowerlessSourceGraphAbsolute.map_l hUT).mp hf
    exact ⟨n.val, hn, PowerlessFunction.range_l hℳ hf₀
      (fun _ _ hxy => hUT A.val _ A.property (PowerlessFunction.value_mem_l hℳ hf₀ hxy).2)⟩
  · rintro ⟨n, hn, hf⟩
    obtain ⟨A, hfA⟩ := range_l hℳ hω ht hT hU hδ hf
    exact ⟨⟨n, hUT ω.val n ω.property hn⟩, A, hn,
      (PowerlessSourceGraphAbsolute.map_l hUT).mpr hfA⟩

theorem slot_l {f i : type_l U} :
    PowerlessAmbientAssignments.slot_l (ℳ := structure_l U hU₀) ω f i ↔
      ∃ n, member_l ℳ n ω.val ∧ map_l f.val n U ∧ member_l ℳ i.val n := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  constructor
  · rintro ⟨n, A, hn, hf, hi⟩
    have hf₀ := (PowerlessSourceGraphAbsolute.map_l hUT).mp hf
    exact ⟨n.val, hn, PowerlessFunction.range_l hℳ hf₀
      (fun _ _ hxy => hUT A.val _ A.property (PowerlessFunction.value_mem_l hℳ hf₀ hxy).2), hi⟩
  · rintro ⟨n, hn, hf, hi⟩
    obtain ⟨A, hfA⟩ := range_l hℳ hω ht hT hU hδ hf
    exact ⟨⟨n, hUT ω.val n ω.property hn⟩, A, hn,
      (PowerlessSourceGraphAbsolute.map_l hUT).mpr hfA, hi⟩

theorem finite_source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w f : Term ℒ Γ Δ .set) (hw : (w.eval η).val = ω.val) :
    (PowerlessAmbientAssignments.finite_m w f).satisfies η ↔
      ∃ n, member_l ℳ n ω.val ∧ map_l (f.eval η).val n U := by
  rw [PowerlessAmbientAssignments.finite_formula_l, Subtype.ext hw]
  exact finite_l hℳ hω ht hT hU hδ

theorem slot_source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w f i : Term ℒ Γ Δ .set) (hw : (w.eval η).val = ω.val) :
    (PowerlessAmbientAssignments.slot_m w f i).satisfies η ↔
      ∃ n, member_l ℳ n ω.val ∧ map_l (f.eval η).val n U ∧ member_l ℳ (i.eval η).val n := by
  rw [PowerlessAmbientAssignments.slot_formula_l, Subtype.ext hw]
  exact slot_l hℳ hω ht hT hU hδ

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageAmbientAssignments
