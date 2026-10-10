import BMSConstructibleBridge.PowerlessDiagramRelabelConditions
import BMSConstructibleBridge.PowerlessFiniteDiagramSource

/-!
# 原共同重标号矩阵的完整逐块源解释

好标签、两类序边、两类具名稳定边及顶端稳定迹使用同一个实际函数 g。
有限列表只索引外部固定层号；图的内部定义域不要求标准。
本模块解释已有矩阵，不把这些条件的共同可满足性作为已经完成的结论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelabelSource

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure PowerlessRelabelMatrix

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 原重标号条件的实际集合语义；所有关系同时读取同一 g。 -/
def conditions_l (ω e T t₁ t₂ t₃ c N δ f g D E : carrier_l ℳ)
    (Ψ : List (carrier_l ℳ × carrier_l ℳ × carrier_l ℳ))
    (Θ : List (carrier_l ℳ × carrier_l ℳ)) : Prop :=
  (∀ i a, value_l g i a → PowerlessCodedDiagram.good_l ω e T t₁ t₂ t₃ c N a) ∧
  PowerlessDiagramRelabelConditions.preserves_l (member_l ℳ) D f g ∧
  PowerlessDiagramRelabelConditions.preserves_l (member_l ℳ) E g g ∧
  (∀ p ∈ Ψ,
    PowerlessDiagramRelabelConditions.preserves_l
      (PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ p.1) p.2.1 f g ∧
    PowerlessDiagramRelabelConditions.preserves_l
      (PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ p.1) p.2.2 g g) ∧
  ∀ p ∈ Θ, ∀ i, member_l ℳ i p.2 → ∀ a, value_l g i a →
    PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ p.1 a δ

theorem source_l {U δ R H : carrier_l ℳ} {hU₀ : ∃ x, member_l ℳ x U}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val)
    (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
    (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
    (hU : PowerlessStageEvaluation.system_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U R H)
    (hδ : PowerlessStagePair.limit_l δ) (hωδ : member_l ℳ ω.val δ)
    (k : Nat) (h𝒰 : Theory.Models (structure_l U hU₀)
      (Theory.ofList (PowerlessStabilitySupport.basis_m k)))
    {Δ : SortContext ℒ} (η : Env (structure_l U hU₀) [] Δ)
    (w z V s₁ s₂ s₃ c N q f D E : Term ℒ [] Δ .set)
    (Ψ : List (edge_m Δ)) (Θ : List (trace_m Δ))
    (hw : (w.eval η).val = ω.val) (hz : (z.eval η).val = e.val)
    (hV : (V.eval η).val = T.val) (hs₁ : (s₁.eval η).val = t₁.val)
    (hs₂ : (s₂.eval η).val = t₂.val) (hs₃ : (s₃.eval η).val = t₃.val)
    (hN : member_l ℳ (N.eval η).val ω.val)
    (hΘ : ∀ p ∈ Θ, p.1 ≤ k ∧
      PowerlessNumeral.numeral_l e.val p.1 (p.2.1.eval η).val ∧
      subset_l (p.2.2.eval η).val (q.eval η).val)
    (g B : type_l U) (hg : map_l g.val (q.eval η).val B.val) :
    (∀ φ ∈ matrix_m w z V s₁ s₂ s₃ c N q f D E Ψ Θ,
      φ.satisfies ((η.pushBound g).pushBound B)) ↔
      conditions_l ω.val e.val T.val t₁.val t₂.val t₃.val (c.eval η).val (N.eval η).val δ
        (f.eval η).val g.val (D.eval η).val (E.eval η).val
        (Ψ.map (fun p => ((p.1.eval η).val, (p.2.1.eval η).val, (p.2.2.eval η).val)))
        (Θ.map (fun p => ((p.2.1.eval η).val, (p.2.2.eval η).val))) := by
  let ζ : Env (structure_l U hU₀) [.set, .set] Δ := (η.pushBound g).pushBound B
  have hη : PowerlessDiagramConstraint.parameters_l ζ = η := by
    apply Env.ext (bound := []) (fun {_} v => nomatch v)
    · intro s v
      rfl
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU.1
  have h𝒩 := PowerlessStabilitySupport.hierarchy_l h𝒰
  have hw₀ : (w.eval (PowerlessDiagramConstraint.parameters_l ζ)).val = ω.val := by
    simpa only [hη] using hw
  have hz₀ : (z.eval (PowerlessDiagramConstraint.parameters_l ζ)).val = e.val := by
    simpa only [hη] using hz
  have hV₀ : (V.eval (PowerlessDiagramConstraint.parameters_l ζ)).val = T.val := by
    simpa only [hη] using hV
  have hs₀ : (s₁.eval (PowerlessDiagramConstraint.parameters_l ζ)).val = t₁.val := by
    simpa only [hη] using hs₁
  have hs₄ : (s₂.eval (PowerlessDiagramConstraint.parameters_l ζ)).val = t₂.val := by
    simpa only [hη] using hs₂
  have hs₅ : (s₃.eval (PowerlessDiagramConstraint.parameters_l ζ)).val = t₃.val := by
    simpa only [hη] using hs₃
  have hg₀ : map_l (graph_m.eval ζ).val ((lift_m q).eval ζ).val B.val := by
    simpa only [ζ, graph_l, lift_l] using hg
  have hC := PowerlessCodedDiagram.labels_source_l hℳ hω ht hT hU.1 hδ hωδ h𝒩
    ζ w z V s₁ s₂ s₃ c N graph_m (lift_m q) hw₀ hz₀ hV₀ hs₀ hs₄ hs₅
    (by simpa only [hη] using hN) hg₀
  rw [matrix_formula_l, conditions_l]
  simp only [List.forall_mem_map]
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_)))
  · simpa only [hη, ζ, graph_l, lift_l] using hC
  · simpa only [ζ, graph_l, lift_l] using
      PowerlessDiagramRelabelConditions.order_source_l hUT ζ (lift_m D) (lift_m f) graph_m
  · simpa only [ζ, graph_l, lift_l] using
      PowerlessDiagramRelabelConditions.order_source_l hUT ζ (lift_m E) graph_m graph_m
  · apply forall_congr'
    intro p
    apply forall_congr'
    intro _
    refine and_congr ?_ ?_
    · simpa only [hη, ζ, graph_l, lift_l] using
        PowerlessDiagramRelabelConditions.stable_source_l hℳ hω ht hT hU.1 hδ h𝒩 hωδ
          ζ w z V s₁ s₂ s₃ p.1 (lift_m p.2.1) (lift_m f) graph_m hw₀ hz₀ hV₀ hs₀ hs₄ hs₅
    · simpa only [hη, ζ, graph_l, lift_l] using
        PowerlessDiagramRelabelConditions.stable_source_l hℳ hω ht hT hU.1 hδ h𝒩 hωδ
          ζ w z V s₁ s₂ s₃ p.1 (lift_m p.2.2) graph_m graph_m hw₀ hz₀ hV₀ hs₀ hs₄ hs₅
  · apply forall_congr'
    intro p
    apply forall_congr'
    intro hp
    obtain ⟨hpk, hn, hD⟩ := hΘ p hp
    have h := PowerlessAmbientDiagram.source_l hℳ hω ht hT hU hδ hωδ p.1
      (PowerlessStabilitySupport.monotone_l hpk h𝒰) ζ w z V s₁ s₂ s₃ p.2.1
      graph_m (lift_m p.2.2) hw₀ hz₀ hV₀ hs₀ hs₄ hs₅
      (by simpa only [hη] using hn) hg₀
      (by simpa only [ζ, lift_l] using hD)
    simpa only [hη, ζ, graph_l, lift_l] using h

/-- 共同存在式恰好是落在当前层的一张内部有限图满足全部原条件。
实际有限图与其实际值域的成员性由已证明的闭包补齐，不作为额外前提。
-/
theorem realize_l {U δ R H : carrier_l ℳ} {hU₀ : ∃ x, member_l ℳ x U}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val)
    (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
    (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
    (hU : PowerlessStageEvaluation.system_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U R H)
    (hδ : PowerlessStagePair.limit_l δ) (hωδ : member_l ℳ ω.val δ)
    (k : Nat) (h𝒰 : Theory.Models (structure_l U hU₀)
      (Theory.ofList (PowerlessStabilitySupport.basis_m k)))
    {Δ : SortContext ℒ} (η : Env (structure_l U hU₀) [] Δ)
    (w z V s₁ s₂ s₃ c N q f D E : Term ℒ [] Δ .set)
    (Ψ : List (edge_m Δ)) (Θ : List (trace_m Δ))
    (hw : (w.eval η).val = ω.val) (hz : (z.eval η).val = e.val)
    (hV : (V.eval η).val = T.val) (hs₁ : (s₁.eval η).val = t₁.val)
    (hs₂ : (s₂.eval η).val = t₂.val) (hs₃ : (s₃.eval η).val = t₃.val)
    (hN : member_l ℳ (N.eval η).val ω.val) (hq : member_l ℳ (q.eval η).val ω.val)
    (hΘ : ∀ p ∈ Θ, p.1 ≤ k ∧
      PowerlessNumeral.numeral_l e.val p.1 (p.2.1.eval η).val ∧
      subset_l (p.2.2.eval η).val (q.eval η).val) :
    (formula_m w z V s₁ s₂ s₃ c N q f D E Ψ Θ).satisfies η ↔
      ∃ g, map_l g (q.eval η).val U ∧
        conditions_l ω.val e.val T.val t₁.val t₂.val t₃.val (c.eval η).val (N.eval η).val δ
          (f.eval η).val g (D.eval η).val (E.eval η).val
          (Ψ.map (fun p => ((p.1.eval η).val, (p.2.1.eval η).val, (p.2.2.eval η).val)))
          (Θ.map (fun p => ((p.2.1.eval η).val, (p.2.2.eval η).val))) := by
  apply PowerlessFiniteDiagramSource.source_l hℳ hω ht hT hU.1 hδ
    (fun x hx => PowerlessOrdinal.transitive_l hδ.1 ω.val x hωδ hx) _ q η hq
  intro g B hg
  exact source_l hℳ hω ht hT hU hδ hωδ k h𝒰 η w z V s₁ s₂ s₃ c N q f D E Ψ Θ
    hw hz hV hs₁ hs₂ hs₃ hN hΘ g B hg

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelabelSource
