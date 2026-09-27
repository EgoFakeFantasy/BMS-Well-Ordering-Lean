import BMSConstructibleBridge.PowerlessRelabelMatrix
import BMSConstructibleBridge.PowerlessValueAbsolute
import BMSConstructibleBridge.PowerlessFiniteStageStability

/-!
# 共同标签图的原二元关系约束

每条指定索引边读取同一 f,g 的实际值。传递性从图值见证取回全部坐标，
故通用解释不需要另加定义域、映射或小层集合论假设。
原稳定关系的实例只使用小层有限层核心，不要求它满足完整 PowerlessTheory。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessDiagramRelabelConditions

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 每个记录的索引对都由两张原图的实际输出实现该关系；允许 f=g。 -/
def preserves_l (r : carrier_l ℳ → carrier_l ℳ → Prop) (D f g : carrier_l ℳ) : Prop :=
  ∀ p, member_l ℳ p D → ∃ i j a b,
    ordered_l i j p ∧ value_l f i a ∧ value_l g j b ∧ r a b

theorem source_l {U : carrier_l ℳ} {hU₀ : ∃ x, member_l ℳ x U}
    (hUT : PowerlessNaturalOrder.transitive_l U)
    {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (structure_l U hU₀) Γ Δ) (D f g : Term ℒ Γ Δ .set)
    (r : carrier_l ℳ → carrier_l ℳ → Prop)
    (hφ : ∀ a b : type_l U,
      φ.satisfies (((PowerlessDiagramConstraint.parameters_l η).pushFree a).pushFree b) ↔
        r a.val b.val) :
    (PowerlessDiagramConstraint.instance_m φ D f g).satisfies η ↔
      preserves_l r (D.eval η).val (f.eval η).val (g.eval η).val := by
  rw [PowerlessDiagramConstraint.instance_formula_l]
  constructor
  · intro h p hp
    obtain ⟨i, j, a, b, hij, ha, hb, h⟩ :=
      h ⟨p, hUT (D.eval η).val p (D.eval η).property hp⟩ hp
    exact ⟨i.val, j.val, a.val, b.val,
      (PowerlessSourceGraphAbsolute.ordered_l hUT).mp hij,
      (PowerlessSourceGraphAbsolute.value_l hUT).mp ha,
      (PowerlessSourceGraphAbsolute.value_l hUT).mp hb, (hφ a b).mp h⟩
  · intro h p hp
    obtain ⟨i, j, a, b, hij, ha, hb, h⟩ := h p.val hp
    obtain ⟨hiU, haU⟩ := PowerlessValueAbsolute.coordinates_l hUT (f.eval η).property ha
    obtain ⟨hjU, hbU⟩ := PowerlessValueAbsolute.coordinates_l hUT (g.eval η).property hb
    exact ⟨⟨i, hiU⟩, ⟨j, hjU⟩, ⟨a, haU⟩, ⟨b, hbU⟩,
      (PowerlessSourceGraphAbsolute.ordered_l hUT).mpr hij,
      (PowerlessSourceGraphAbsolute.value_l hUT).mpr ha,
      (PowerlessSourceGraphAbsolute.value_l hUT).mpr hb, (hφ ⟨a, haU⟩ ⟨b, hbU⟩).mpr h⟩

/-- 顺序是左标签属于右标签，与原低高及高高矩阵一致。 -/
theorem order_source_l {U : carrier_l ℳ} {hU₀ : ∃ x, member_l ℳ x U}
    (hUT : PowerlessNaturalOrder.transitive_l U)
    {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (D f g : Term ℒ Γ Δ .set) :
    (PowerlessDiagramConstraint.instance_m PowerlessRelabelMatrix.order_m D f g).satisfies η ↔
      preserves_l (member_l ℳ) (D.eval η).val (f.eval η).val (g.eval η).val :=
  source_l hUT _ η D f g _ (fun _ _ => Iff.rfl)

/-- 任意内部层号的原稳定关系；不把小层有限核心升级成完整理论。 -/
theorem stable_source_l {U δ : carrier_l ℳ} {hU₀ : ∃ x, member_l ℳ x U}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val)
    (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
    (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
    (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U)
    (hδ : PowerlessStagePair.limit_l δ)
    (h𝒩 : Theory.Models (structure_l U hU₀) PowerlessFiniteStageHierarchy.theory_m)
    (hωδ : member_l ℳ ω.val δ)
    {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w z V s₁ s₂ s₃ n : Term ℒ [] Δ .set) (D f g : Term ℒ Γ Δ .set)
    (hw : (w.eval (PowerlessDiagramConstraint.parameters_l η)).val = ω.val)
    (hz : (z.eval (PowerlessDiagramConstraint.parameters_l η)).val = e.val)
    (hV : (V.eval (PowerlessDiagramConstraint.parameters_l η)).val = T.val)
    (hs₁ : (s₁.eval (PowerlessDiagramConstraint.parameters_l η)).val = t₁.val)
    (hs₂ : (s₂.eval (PowerlessDiagramConstraint.parameters_l η)).val = t₂.val)
    (hs₃ : (s₃.eval (PowerlessDiagramConstraint.parameters_l η)).val = t₃.val) :
    (PowerlessDiagramConstraint.instance_m
      (PowerlessStableDiagram.relation_m w z V s₁ s₂ s₃ n) D f g).satisfies η ↔
      preserves_l (PowerlessStageStability.stable_l ω.val e.val T.val t₁.val t₂.val t₃.val
        (n.eval (PowerlessDiagramConstraint.parameters_l η)).val)
        (D.eval η).val (f.eval η).val (g.eval η).val := by
  apply source_l (PowerlessStageStructure.transitive_l hℳ hω ht hT hU) _ η D f g
  intro a b
  let w₀ (t : Term ℒ [] Δ .set) :=
    (t.weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set
  have h := PowerlessFiniteStageStability.source_l hℳ hω ht hT hU hδ h𝒩 hωδ
    (((PowerlessDiagramConstraint.parameters_l η).pushFree a).pushFree b)
    (w₀ w) (w₀ z) (w₀ V) (w₀ s₁) (w₀ s₂) (w₀ s₃) (w₀ n)
    (.fvar (.there .here)) (.fvar .here)
    (by simpa only [w₀, Term.eval_weakenFree] using hw)
    (by simpa only [w₀, Term.eval_weakenFree] using hz)
    (by simpa only [w₀, Term.eval_weakenFree] using hV)
    (by simpa only [w₀, Term.eval_weakenFree] using hs₁)
    (by simpa only [w₀, Term.eval_weakenFree] using hs₂)
    (by simpa only [w₀, Term.eval_weakenFree] using hs₃)
  simp only [w₀, Term.eval_weakenFree] at h
  simpa only [PowerlessStableDiagram.relation_m, Term.eval, Env.pushFree, Assignment.push] using h

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessDiagramRelabelConditions
