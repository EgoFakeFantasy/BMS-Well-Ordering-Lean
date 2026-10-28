import BMSConstructibleBridge.PowerlessOrdinalRecursionAbsolute
import BMSConstructibleBridge.PowerlessStageOrdinalRelation
import BMSConstructibleBridge.PowerlessEvaluationAbsolute
import BMSConstructibleBridge.PowerlessEvaluationPresentation

/-!
# 原求值公式在实际极限层中的正确解释

原 evaluation_m 和其内部递归模板保持不变。先显式提供域内关系图 R，
再接原语义求值的绝对性。实际层出口消去 R 存在和关系对闭包条件；
赋值集合 S 与候选求值图 F 仍是域内参数，不宣称其整体早级成员性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationSourceAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)

include hℳ

theorem source_l {B : carrier_l ℳ} {hB : ∃ x, member_l ℳ x B}
    (hBT : PowerlessNaturalOrder.transitive_l B) {Γ Δ : SortContext ℒ}
    (η : Env (structure_l B hB) Γ Δ) (ω e T A t₁ t₂ t₃ S F : Term ℒ Γ Δ .set)
    (hR : ∃ R : type_l B, PowerlessOrdinalRelation.relation_l (ω.eval η).val R.val) :
    (PowerlessEvaluationPresentation.evaluation_m ω e T A t₁ t₂ t₃ S F).satisfies η ↔
      PowerlessEvaluationRecursion.evaluation_l (ω.eval η) (e.eval η) (T.eval η) (A.eval η)
        (t₁.eval η) (t₂.eval η) (t₃.eval η) (S.eval η) (F.eval η) := by
  rw [← PowerlessEvaluationRecursion.recursion_iff_l,
    ← PowerlessOrdinalRecursionAbsolute.source_l hℳ hBT PowerlessEvaluationStep.operator_m _ _ _ hR]
  simp only [PowerlessEvaluationPresentation.evaluation_m, Formula.satisfies_substitute]
  apply Iff.of_eq
  apply congrArg (fun η => (PowerlessOrdinalRecursion.recursion_m PowerlessEvaluationStep.operator_m).satisfies η)
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    rcases v with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | v
    all_goals first | rfl | nomatch v

theorem stage_l {ω e T t₁ t₂ t₃ β B : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hB : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ β B)
    (hωβ : member_l ℳ ω β) (hβ : PowerlessStagePair.limit_l β)
    {hB₀ : ∃ x, member_l ℳ x B} {Γ Δ : SortContext ℒ} (η : Env (structure_l B hB₀) Γ Δ)
    (w z U A s₁ s₂ s₃ S F : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω) (hz : (z.eval η).val = e) (hU : (U.eval η).val = T)
    (h₁ : (s₁.eval η).val = t₁) (h₂ : (s₂.eval η).val = t₂) (h₃ : (s₃.eval η).val = t₃) :
    (PowerlessEvaluationPresentation.evaluation_m w z U A s₁ s₂ s₃ S F).satisfies η ↔
      PowerlessEvaluationRecursion.evaluation_l ω e T (A.eval η).val t₁ t₂ t₃ (S.eval η).val (F.eval η).val := by
  have hBT := PowerlessStageStructure.transitive_l hℳ hω ht hT hB
  obtain ⟨R, hR, hRB⟩ := PowerlessStageOrdinalRelation.exists_l hℳ hω ht hT hB hωβ hβ
  have hR₀ : ∃ R : type_l B, PowerlessOrdinalRelation.relation_l (w.eval η).val R.val := by
    refine ⟨⟨R, hRB⟩, ?_⟩
    simpa only [hw] using hR
  obtain ⟨hB₁, w₁, z₁, U₁, r₁, r₂, r₃, hw₁, hz₁, hU₁, hr₁, hr₂, hr₃, hE⟩ :=
    PowerlessEvaluationAbsolute.stage_l hℳ hω ht hT hB hωβ hβ
  have hw₂ : w.eval η = w₁ := Subtype.ext (hw.trans hw₁.symm)
  have hz₂ : z.eval η = z₁ := Subtype.ext (hz.trans hz₁.symm)
  have hU₂ : U.eval η = U₁ := Subtype.ext (hU.trans hU₁.symm)
  have hs₁ : s₁.eval η = r₁ := Subtype.ext (h₁.trans hr₁.symm)
  have hs₂ : s₂.eval η = r₂ := Subtype.ext (h₂.trans hr₂.symm)
  have hs₃ : s₃.eval η = r₃ := Subtype.ext (h₃.trans hr₃.symm)
  rw [← hw₂, ← hz₂, ← hU₂, ← hs₁, ← hs₂, ← hs₃] at hE
  exact (source_l hℳ hBT η w z U A s₁ s₂ s₃ S F hR₀).trans (hE (A.eval η) (S.eval η) (F.eval η))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationSourceAbsolute
