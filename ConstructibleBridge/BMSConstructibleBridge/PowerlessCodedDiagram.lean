import BMSConstructibleBridge.PowerlessDiagramLabels
import BMSConstructibleBridge.PowerlessCodedStageSource
import BMSConstructibleBridge.PowerlessStagePairAbsolute

/-!
# 同一重标号图的全部好标签条件

固定原公式对图的每个实际输出读取层理论数码，而非检查一个固定自由标签。
内部下标长度 q 与数码求值长度 N 是不同参数。支持理论只改变 c,N 的值，
不改变本模块的公式正文；小层仅要求有限层核心。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCodedDiagram

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def good_l (ω e T t₁ t₂ t₃ c N α : carrier_l ℳ) : Prop :=
  member_l ℳ ω α ∧ PowerlessStagePair.limit_l α ∧
    PowerlessCodedStageTheory.holds_l ω e T t₁ t₂ t₃ c N α

def good_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ c N α : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (SecondOrderObjectSyntax.member_m ω α) (.conj (PowerlessStagePair.limit_m α)
    (PowerlessCodedStageTheory.holds_m ω e T t₁ t₂ t₃ c N α))

theorem good_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ c N α : Term ℒ Γ Δ .set) :
    (good_m ω e T t₁ t₂ t₃ c N α).satisfies η ↔
      good_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
        (c.eval η) (N.eval η) (α.eval η) := by
  simp only [good_m, good_l, Formula.satisfies, PowerlessStagePair.limit_formula_l hℳ,
    PowerlessCodedStageTheory.holds_formula_l hℳ, SecondOrderObjectSyntax.member_m, Arguments.eval]
  rfl

/-- 序数 guard 从层的真实序数截面推出标签严格低于读取层，不另加这一前提。 -/
theorem good_source_l {U δ : carrier_l ℳ} {hU₀ : ∃ x, member_l ℳ x U}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val)
    (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
    (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
    (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U)
    (hδ : PowerlessStagePair.limit_l δ) (hωδ : member_l ℳ ω.val δ)
    (h𝒩 : Theory.Models (structure_l U hU₀) PowerlessFiniteStageHierarchy.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w z V s₁ s₂ s₃ c N α : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω.val) (hz : (z.eval η).val = e.val)
    (hV : (V.eval η).val = T.val) (hs₁ : (s₁.eval η).val = t₁.val)
    (hs₂ : (s₂.eval η).val = t₂.val) (hs₃ : (s₃.eval η).val = t₃.val)
    (hN : member_l ℳ (N.eval η).val ω.val) :
    (good_m w z V s₁ s₂ s₃ c N α).satisfies η ↔
      good_l ω.val e.val T.val t₁.val t₂.val t₃.val (c.eval η).val (N.eval η).val (α.eval η).val := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  have hW : (SecondOrderObjectSyntax.member_m w α).satisfies η ↔
      member_l ℳ ω.val (α.eval η).val := by
    change member_l ℳ (w.eval η).val (α.eval η).val ↔ _
    rw [hw]
  simp only [good_m, good_l, Formula.satisfies]
  rw [hW, PowerlessStagePairAbsolute.limit_l hℳ hUT η α]
  apply and_congr Iff.rfl
  apply and_congr_right
  intro hα
  exact PowerlessCodedStageSource.holds_source_l hℳ hω ht hT hU hδ h𝒩 hωδ
    η w z V s₁ s₂ s₃ c N α hw hz hV hs₁ hs₂ hs₃ hN
    ((PowerlessStageOrdinal.member_l hℳ hω ht hT hU hα.1).mp (α.eval η).property)

/-- 新自由槽就是当前输出标签；原八项只承载系统参数与统一数码。 -/
def condition_m {Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ c N : Term ℒ [] Δ .set) :
    Formula ℒ [] (.set :: Δ) :=
  good_m (ω.weakenFree SetTheory.SetSort.set) (e.weakenFree SetTheory.SetSort.set)
    (T.weakenFree SetTheory.SetSort.set) (t₁.weakenFree SetTheory.SetSort.set)
    (t₂.weakenFree SetTheory.SetSort.set) (t₃.weakenFree SetTheory.SetSort.set)
    (c.weakenFree SetTheory.SetSort.set) (N.weakenFree SetTheory.SetSort.set) (.fvar .here)

def labels_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ c N : Term ℒ [] Δ .set)
    (g q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  PowerlessDiagramLabels.labels_m (condition_m ω e T t₁ t₂ t₃ c N) g q

/-- 单个固定矩阵精确约束同一实际函数图的全部输出，覆盖非标准内部长度。
此处不声称已经构造满足全部 BMS 边及序条件的共同见证。 -/
theorem labels_source_l {U δ : carrier_l ℳ} {hU₀ : ∃ x, member_l ℳ x U}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val)
    (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
    (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
    (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U)
    (hδ : PowerlessStagePair.limit_l δ) (hωδ : member_l ℳ ω.val δ)
    (h𝒩 : Theory.Models (structure_l U hU₀) PowerlessFiniteStageHierarchy.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w z V s₁ s₂ s₃ c N : Term ℒ [] Δ .set) (g q : Term ℒ Γ Δ .set)
    (hw : (w.eval (PowerlessDiagramConstraint.parameters_l η)).val = ω.val)
    (hz : (z.eval (PowerlessDiagramConstraint.parameters_l η)).val = e.val)
    (hV : (V.eval (PowerlessDiagramConstraint.parameters_l η)).val = T.val)
    (hs₁ : (s₁.eval (PowerlessDiagramConstraint.parameters_l η)).val = t₁.val)
    (hs₂ : (s₂.eval (PowerlessDiagramConstraint.parameters_l η)).val = t₂.val)
    (hs₃ : (s₃.eval (PowerlessDiagramConstraint.parameters_l η)).val = t₃.val)
    (hN : member_l ℳ (N.eval (PowerlessDiagramConstraint.parameters_l η)).val ω.val)
    {B : type_l U} (hg : map_l (g.eval η).val (q.eval η).val B.val) :
    (labels_m w z V s₁ s₂ s₃ c N g q).satisfies η ↔
      ∀ i a, value_l (g.eval η).val i a →
        good_l ω.val e.val T.val t₁.val t₂.val t₃.val
          (c.eval (PowerlessDiagramConstraint.parameters_l η)).val
          (N.eval (PowerlessDiagramConstraint.parameters_l η)).val a := by
  apply PowerlessDiagramLabels.source_l hℳ
    (PowerlessStageStructure.transitive_l hℳ hω ht hT hU) _ η g q hg
  intro a
  have h := good_source_l hℳ hω ht hT hU hδ hωδ h𝒩
    ((PowerlessDiagramConstraint.parameters_l η).pushFree a)
    (w.weakenFree SetTheory.SetSort.set) (z.weakenFree SetTheory.SetSort.set)
    (V.weakenFree SetTheory.SetSort.set) (s₁.weakenFree SetTheory.SetSort.set)
    (s₂.weakenFree SetTheory.SetSort.set) (s₃.weakenFree SetTheory.SetSort.set)
    (c.weakenFree SetTheory.SetSort.set) (N.weakenFree SetTheory.SetSort.set) (.fvar .here)
    (by simpa only [Term.eval_weakenFree] using hw)
    (by simpa only [Term.eval_weakenFree] using hz)
    (by simpa only [Term.eval_weakenFree] using hV)
    (by simpa only [Term.eval_weakenFree] using hs₁)
    (by simpa only [Term.eval_weakenFree] using hs₂)
    (by simpa only [Term.eval_weakenFree] using hs₃)
    (by simpa only [Term.eval_weakenFree] using hN)
  simp only [Term.eval_weakenFree] at h
  simpa only [condition_m, Term.eval, Env.pushFree, Assignment.push] using h

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCodedDiagram
