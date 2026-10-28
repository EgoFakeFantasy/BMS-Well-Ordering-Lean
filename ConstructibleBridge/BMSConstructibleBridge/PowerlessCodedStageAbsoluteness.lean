import BMSConstructibleBridge.PowerlessCodedStageTheory
import BMSConstructibleBridge.PowerlessCoreStageSystem
import BMSConstructibleBridge.PowerlessSourceGraphAbsolute
import BMSConstructibleBridge.PowerlessValueAbsolute
import BMSConstructibleBridge.PowerlessStageFiniteGraphs

/-!
# 编码层理论公式在小层内的绝对性

补齐 §16 条目 3 的缺口：先把"长度 ∈ ω、值落在 A ∈ U"的实际赋值图吸收进传递上层 U
（finite_l + range_l 组合），再用原层系统、映射与查询的现成绝对性桥
给出 holds_m 的 holds_l 跨层等价。全部假设与层参数保持公开，不新增公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCodedStageAbsoluteness

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure PowerlessCodedStageTheory

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U δ : carrier_l ℳ}
  {hU₀ : ∃ x, ThirdOrderSemantics.member_l ℳ x U} (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val)
  (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
  (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
  (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U)
  (hδ : PowerlessStagePair.limit_l δ)
  (h𝒩 : Theory.Models (structure_l U hU₀) PowerlessTheory.theory_m)
  (hωδ : ThirdOrderSemantics.member_l ℳ ω.val δ)

include hℳ hω ht hT hU hδ h𝒩 hωδ

omit h𝒩 in
/-- 赋值图吸收：内部自然数长度、值域落在 U 内元素 A 中的实际图整体属于传递上层 U。 -/
lemma graph_member_l {N A f : carrier_l ℳ} (hN : member_l ℳ N ω.val)
    (hA : member_l ℳ A U) (hf : map_l f N A) : member_l ℳ f U := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  have hωδ₀ : subset_l ω.val δ := fun a ha => PowerlessOrdinal.transitive_l hδ.1 ω.val a hωδ ha
  exact PowerlessStageFiniteGraphs.finite_l hℳ hω ht hT hU hδ hωδ₀ N hN f
    (PowerlessFunction.range_l hℳ hf
      (fun _ a ha => hUT A a hA (PowerlessFunction.value_mem_l hℳ hf ha).2))

/-- 编码满足式的跨层绝对性：小结构内成立当且仅当环境层内成立。 -/
theorem holds_absolute_l {c N α : type_l U} (hN : member_l ℳ N.val ω.val)
    (hα : member_l ℳ α.val δ) :
    holds_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ c N α ↔
      holds_l ω.val e.val T.val t₁.val t₂.val t₃.val c.val N.val α.val := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  constructor
  · rintro ⟨A, S, F, hsys, ⟨f, hf, hq⟩⟩
    exact ⟨A.val, S.val, F.val,
      (PowerlessCoreStageSystem.system_l (hU₀ := hU₀) hℳ hω ht hT hU hδ h𝒩 hωδ).mp hsys,
      ⟨f.val, (PowerlessSourceGraphAbsolute.map_l hUT).mp hf,
        (PowerlessValueAbsolute.query_l hUT).mp hq⟩⟩
  · intro h
    obtain ⟨A, S, F, hsys, ⟨f, hf, hq⟩⟩ := h
    have hASF := PowerlessCoreStageSystem.member_l hℳ hω ht hT hU hδ h𝒩 hωδ hα hsys
    have hfU : member_l ℳ f U := graph_member_l hℳ hω ht hT hU hδ hωδ hN hASF.1 hf
    exact ⟨⟨A, hASF.1⟩, ⟨S, hASF.2.1⟩, ⟨F, hASF.2.2⟩,
      (PowerlessCoreStageSystem.system_l (hU₀ := hU₀) hℳ hω ht hT hU hδ h𝒩 hωδ).mpr hsys,
      ⟨⟨f, hfU⟩, (PowerlessSourceGraphAbsolute.map_l hUT).mpr hf,
        (PowerlessValueAbsolute.query_l hUT).mpr hq⟩⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCodedStageAbsoluteness
