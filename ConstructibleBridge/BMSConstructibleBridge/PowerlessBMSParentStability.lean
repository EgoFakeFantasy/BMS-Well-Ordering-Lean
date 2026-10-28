import BMSConstructibleBridge.PowerlessBMSRepresentation
import BMSConstructibleBridge.PowerlessNumeralOrder
import BMSConstructibleBridge.SecondOrderProgramMaximalParentHeight
import BMSConstructibleBridge.SecondOrderProgramUniformAncestorStructure

/-!
# 从真实父边取得有限层反射参数

实际父行严格低于数组高度；固定外部行界以下的内部行可解码为较小的外部数码。
原标签表示于是直接给出父列与末列标签之间的对应稳定层，同时实际取出两端标签。
不预设反射参数存在，不把模型内部的任意自然数解码为外部 Nat。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSParentStability

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderProgramSemantics
open PrimitiveProgram (graph_m)

set_option autoImplicit false

attribute [local implicit_reducible] PowerlessArithmetic.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  {ω e : carrier_l ℳ} {he : PowerlessNatural.zero_l e} {h₀ : member_l ℳ e ω}
  {F : PowerlessArithmetic.operations_l ω e}

local notation "𝒩" => PowerlessArithmetic.structure_l he h₀ F

/-- 固定行界内的实际父行提供原表示中的两个好标签及正确预算下的稳定对。 -/
theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    {P M J O L E : PowerlessArithmetic.set_l ω}
    (hP : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramUniformParent.parent_m) P)
    (hM : graph_semantics_l (ℳ := 𝒩) (graph_m PowerlessBMSAncestor.program_m) M)
    (hJ : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramEntry.entry_m) J)
    (hO : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramOptionalLookup.optional_m) O)
    (hL : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramLength.length_m) L)
    (hE : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramListLookup.lookup_m) E)
    {T t₁ t₂ t₃ c N σ f bound : carrier_l ℳ} {H : Nat}
    {x last p row height : PowerlessArithmetic.num_l ω}
    (hx : SecondOrderProgramRectangular.rectangular_l (ℳ := 𝒩) L E x (F.succ_l last) height)
    (hparent : SecondOrderPairing.relation_l (ℳ := 𝒩) P
      (SecondOrderPairing.value_l (SecondOrderPairing.value_l x row) last) (SecondOrderModel.succ_l p))
    (hbound : PowerlessNumeral.numeral_l e H bound) (hheight : subset_l height.val bound)
    (hG : PowerlessBMSRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
      T t₁ t₂ t₃ c N H x (F.succ_l last) σ f) :
    ∃ α β k n, k < H ∧ PowerlessNumeral.numeral_l e k row.val ∧
      PowerlessNumeral.numeral_l e (PowerlessRelabelLevels.level_m (H + 1) k) n ∧
      value_l f p.val α ∧ value_l f last.val β ∧
      PowerlessGoodBoundary.stable_l ω e T t₁ t₂ t₃ c N n α β := by
  have h𝒩 := PowerlessArithmeticComprehension.models_l hℳ hω (he := he) (h₀ := h₀) (F := F)
  have hrow := SecondOrderProgramMaximalParentHeight.maximal_lt_height_l h𝒩 hP hJ hO hL hE hx hparent
  have hrowMem := (PowerlessArithmeticOrder.lt_l hℳ hω (he := he) (h₀ := h₀) (F := F) row height).mp hrow
  obtain ⟨k, hk, hnum⟩ := PowerlessNumeralOrder.bounded_l he hbound (hheight row.val hrowMem)
  have hp := SecondOrderProgramUniformParentOrder.parent_lt_l h𝒩 hP hparent
  have hpMem := (PowerlessArithmeticOrder.lt_l hℳ hω (he := he) (h₀ := h₀) (F := F) p last).mp hp
  obtain ⟨α, ⟨_, hα⟩, _⟩ := hG.map_l.2 p.val ((F.succ_graph_l last p.val).mpr (Or.inl hpMem))
  obtain ⟨β, ⟨_, hβ⟩, _⟩ := hG.map_l.2 last.val ((F.succ_graph_l last last.val).mpr (Or.inr rfl))
  have hancestor := (PowerlessBMSAncestor.graph_l hM x row last p).mpr
    (SecondOrderProgramUniformAncestorStructure.parent_l h𝒩 hP hM hparent)
  obtain ⟨n, hn, hstable⟩ := hG.edge_l k hk row hnum p last hancestor α β hα hβ
  exact ⟨α, β, k, n, hk, hnum, hn, hα, hβ, hG.labels_l p.val α hα, hG.labels_l last.val β hβ, hstable⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSParentStability
