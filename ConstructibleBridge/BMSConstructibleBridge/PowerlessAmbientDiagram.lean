import BMSConstructibleBridge.PowerlessDiagramLabels
import BMSConstructibleBridge.PowerlessAmbientStability
import BMSConstructibleBridge.PowerlessStabilitySupport

/-!
# 共同标签图到当前读取层的原稳定迹约束

记录 D 只挑选原来稳定于上端点的内部下标；公式对同一 g 的对应值
读取当前域真值，不把旧上端点或其完整求值图作为低层参数。
外部层号 k 决定原部分真值公式，内部列数与迹 D 均保持为集合。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessAmbientDiagram

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

def condition_m (k : Nat) {Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ n : Term ℒ [] Δ .set) :
    Formula ℒ [] (.set :: Δ) :=
  PowerlessAmbientStability.stable_m k
    (ω.weakenFree SetTheory.SetSort.set) (e.weakenFree SetTheory.SetSort.set)
    (T.weakenFree SetTheory.SetSort.set) (t₁.weakenFree SetTheory.SetSort.set)
    (t₂.weakenFree SetTheory.SetSort.set) (t₃.weakenFree SetTheory.SetSort.set)
    (n.weakenFree SetTheory.SetSort.set) (.fvar .here)

def trace_m (k : Nat) {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ n : Term ℒ [] Δ .set)
    (g D : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  PowerlessDiagramLabels.labels_m (condition_m k ω e T t₁ t₂ t₃ n) g D

/-- 在所需有限支持下，每个被选中的实际输出恰好稳定于当前读取层的标签。
源层和反射后的层分别实例化本定理，上端点因此随读取层改变。 -/
theorem source_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {U δ R H : carrier_l ℳ} {hU₀ : ∃ x, member_l ℳ x U}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val)
    (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
    (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
    (hU : PowerlessStageEvaluation.system_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U R H)
    (hδ : PowerlessStagePair.limit_l δ) (hωδ : member_l ℳ ω.val δ)
    (k : Nat) (h𝒰 : Theory.Models (structure_l U hU₀)
      (Theory.ofList (PowerlessStabilitySupport.basis_m k)))
    {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w z V s₁ s₂ s₃ n : Term ℒ [] Δ .set) (g D : Term ℒ Γ Δ .set)
    (hw : (w.eval (PowerlessDiagramConstraint.parameters_l η)).val = ω.val)
    (hz : (z.eval (PowerlessDiagramConstraint.parameters_l η)).val = e.val)
    (hV : (V.eval (PowerlessDiagramConstraint.parameters_l η)).val = T.val)
    (hs₁ : (s₁.eval (PowerlessDiagramConstraint.parameters_l η)).val = t₁.val)
    (hs₂ : (s₂.eval (PowerlessDiagramConstraint.parameters_l η)).val = t₂.val)
    (hs₃ : (s₃.eval (PowerlessDiagramConstraint.parameters_l η)).val = t₃.val)
    (hn : PowerlessNumeral.numeral_l e.val k (n.eval (PowerlessDiagramConstraint.parameters_l η)).val)
    {q : carrier_l ℳ} {B : type_l U} (hg : map_l (g.eval η).val q B.val)
    (hD : ThirdOrderSemantics.subset_l (D.eval η).val q) :
    (trace_m k w z V s₁ s₂ s₃ n g D).satisfies η ↔
      ∀ i, member_l ℳ i (D.eval η).val → ∀ a, value_l (g.eval η).val i a →
        PowerlessStageStability.stable_l ω.val e.val T.val t₁.val t₂.val t₃.val
          (n.eval (PowerlessDiagramConstraint.parameters_l η)).val a δ := by
  apply PowerlessDiagramLabels.trace_source_l hℳ
    (PowerlessStageStructure.transitive_l hℳ hω ht hT hU.1) _ η g D hg hD
  intro a
  have h := PowerlessAmbientStability.source_l hℳ hω ht hT hU.1 hδ hωδ
    (PowerlessStabilitySupport.hierarchy_l h𝒰) (PowerlessStabilitySupport.introduction_l h𝒰)
    hU.2.1 hU.2.2 k (fun j hj => PowerlessStabilitySupport.oracle_l (j := j) h𝒰 hj)
    ((PowerlessDiagramConstraint.parameters_l η).pushFree a)
    (w.weakenFree SetTheory.SetSort.set) (z.weakenFree SetTheory.SetSort.set)
    (V.weakenFree SetTheory.SetSort.set) (s₁.weakenFree SetTheory.SetSort.set)
    (s₂.weakenFree SetTheory.SetSort.set) (s₃.weakenFree SetTheory.SetSort.set)
    (n.weakenFree SetTheory.SetSort.set) (.fvar .here)
    (by rw [Term.eval_weakenFree]; exact Subtype.ext hw)
    (by rw [Term.eval_weakenFree]; exact Subtype.ext hz)
    (by rw [Term.eval_weakenFree]; exact Subtype.ext hV)
    (by rw [Term.eval_weakenFree]; exact Subtype.ext hs₁)
    (by rw [Term.eval_weakenFree]; exact Subtype.ext hs₂)
    (by rw [Term.eval_weakenFree]; exact Subtype.ext hs₃)
    (by simpa only [Term.eval_weakenFree] using hn)
  simp only [Term.eval_weakenFree] at h
  simpa only [condition_m, Term.eval, Env.pushFree, Assignment.push] using h

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessAmbientDiagram
