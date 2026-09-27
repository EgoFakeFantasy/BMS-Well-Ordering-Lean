import BMSConstructibleBridge.PowerlessDiagramFamily
import BMSConstructibleBridge.PowerlessStageFiniteMapping

/-!
# 共同矩阵的内部存在式与实际有限函数图

实际函数的值落在读取层，不等于它已有一个属于该层的陪域。
使用真实值域闭包同时补齐两份成员见证，再将已核验的矩阵语义接入共同存在式。
正文对应是显式语义义务；本定理不预设共同见证存在，也不替代原 BMS 条件核验。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteDiagramSource

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

theorem source_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ α U : carrier_l ℳ} {hU₀ : ∃ x, member_l ℳ x U}
    (hω : omega_l ω) (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (hU : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α U)
    (hα : PowerlessStagePair.limit_l α) (hωα : subset_l ω α)
    {Γ Δ : SortContext ℒ} (Φ : List (Formula ℒ (.set :: .set :: Γ) Δ))
    (q : Term ℒ Γ Δ .set) (η : Env (structure_l U hU₀) Γ Δ)
    (hq : member_l ℳ (q.eval η).val ω) (P : carrier_l ℳ → Prop)
    (hP : ∀ g B : type_l U, map_l g.val (q.eval η).val B.val →
      ((∀ φ ∈ Φ, φ.satisfies ((η.pushBound g).pushBound B)) ↔ P g.val)) :
    (PowerlessDiagramFamily.realize_m Φ q).satisfies η ↔
      ∃ g, map_l g (q.eval η).val U ∧ P g := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  rw [PowerlessDiagramFamily.realize_formula_l]
  constructor
  · rintro ⟨g, B, hg, h⟩
    have hg₀ := (PowerlessSourceGraphAbsolute.map_l hUT).mp hg
    exact ⟨g.val, PowerlessFunction.range_l hℳ hg₀
      (fun _ a ha => hUT B.val a B.property (PowerlessFunction.value_mem_l hℳ hg₀ ha).2),
      (hP g B hg₀).mp h⟩
  · rintro ⟨g, hg, h⟩
    obtain ⟨hgU, B, hBU, hgB, _⟩ :=
      PowerlessStageFiniteMapping.member_l hℳ hω ht hT hU hα hωα hq hg
    let g₀ : type_l U := ⟨g, hgU⟩
    let B₀ : type_l U := ⟨B, hBU⟩
    exact ⟨g₀, B₀, (PowerlessSourceGraphAbsolute.map_l hUT).mpr hgB, (hP g₀ B₀ hgB).mpr h⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteDiagramSource
