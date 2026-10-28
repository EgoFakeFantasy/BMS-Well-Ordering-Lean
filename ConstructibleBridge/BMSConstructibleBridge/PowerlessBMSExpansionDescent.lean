import BMSConstructibleBridge.PowerlessBMSInitialSplit
import BMSConstructibleBridge.PowerlessBMSParentStability
import BMSConstructibleBridge.PowerlessBMSCopyStep
import BMSConstructibleBridge.PowerlessBMSCopyState
import BMSConstructibleBridge.SecondOrderProgramExpansionWidth

/-!
# 有父展开的完整表示严格下降

从原父边取得有限层稳定对，构造初始拆分，然后在固定最终展开上对内部复制号归纳。
最后一次反射覆盖实际完整宽度，得到低于原父列标签的表示。复制号无外部标准性假设。
本模块显式在 PowerlessTheory 中工作，不把它误报为 Z₂ 中的最终良序证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSExpansionDescent

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderModel (add_l mul_l succ_l zero_l)
open SecondOrderProgramSemantics
open PrimitiveProgram (graph_m)
open PowerlessRelabelLevels (level_m)

set_option autoImplicit false

attribute [local implicit_reducible] PowerlessArithmetic.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  {ω e : carrier_l ℳ} {he : PowerlessNatural.zero_l e} {h₀ : member_l ℳ e ω}
  {F : PowerlessArithmetic.operations_l ω e}

local notation "𝒩" => PowerlessArithmetic.structure_l he h₀ F

/-- 对全部内部复制次数，真实有父展开都有上界严格更小的完整标签表示。 -/
theorem selected_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    {X W P I S Trim Z B L E D J Asc M O : PowerlessArithmetic.set_l ω}
    (hX : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramExpansion.expand_m) X)
    (hW : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramMaximalParentRow.maximal_m) W)
    (hP : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramUniformParent.parent_m) P)
    (hI : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramMaximalParentRow.last_index_m) I)
    (hS : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramExpansionSuccess.success_m) S)
    (hTrim : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramTrimArray.trim_m) Trim)
    (hZ : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramTrimHeight.trim_m) Z)
    (hB : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramExpansionSuccess.bad_m) B)
    (hL : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramLength.length_m) L)
    (hE : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramListLookup.lookup_m) E)
    (hD : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramSubtraction.sub_m) D)
    (hJ : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramEntry.entry_m) J)
    (hAsc : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramAscending.ascending_m) Asc)
    (hM : graph_semantics_l (ℳ := 𝒩) (graph_m PowerlessBMSAncestor.program_m) M)
    (hO : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramOptionalLookup.optional_m) O)
    {x last p d k maximal height y : PowerlessArithmetic.num_l ω}
    (hx : SecondOrderProgramRectangular.rectangular_l (ℳ := 𝒩) L E x (succ_l last) height)
    (hmax : SecondOrderPairing.relation_l (ℳ := 𝒩) W x (succ_l maximal))
    (hlast : SecondOrderPairing.relation_l (ℳ := 𝒩) I x last)
    (hparent : SecondOrderPairing.relation_l (ℳ := 𝒩) P
      (SecondOrderPairing.value_l (SecondOrderPairing.value_l x maximal) last) (succ_l p))
    (hd : SecondOrderPairing.relation_l (ℳ := 𝒩) D (SecondOrderPairing.value_l last p) d)
    (hy : SecondOrderPairing.relation_l (ℳ := 𝒩) X (SecondOrderPairing.value_l x k) y)
    {T t₁ t₂ t₃ c N σ source bound : carrier_l ℳ} {H : Nat}
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (hc : PowerlessGoodBoundary.code_l ω e T t₁ t₂ t₃ c N (level_m (H + 1) (H + 1)))
    (hc₀ : member_l ℳ c ω) (hN : member_l ℳ N ω)
    (hbound : PowerlessNumeral.numeral_l e H bound) (hheight : subset_l height.val bound)
    (hG : PowerlessBMSRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
      T t₁ t₂ t₃ c N H x (succ_l (ℳ := 𝒩) last) σ source) :
    ∃ α f, member_l ℳ α σ ∧
      PowerlessBMSRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
        T t₁ t₂ t₃ c N H y (add_l (ℳ := 𝒩) p (mul_l d (succ_l k))) α f := by
  have h𝒩 := PowerlessArithmeticComprehension.models_l hℳ hω (he := he) (h₀ := h₀) (F := F)
  obtain ⟨α, β, rowMax, n, hrow, hrowMax, hn, hα, hβ, hs⟩ :=
    PowerlessBMSParentStability.exists_l hℳ hω hP hM hJ hO hL hE hx hparent hbound hheight hG
  have hpj := SecondOrderProgramUniformParentOrder.parent_lt_l h𝒩 hP hparent
  have hpd : add_l (ℳ := 𝒩) p d = last := by
    rw [SecondOrderNumbers.add_comm_l h𝒩]
    exact SecondOrderProgramSubtractionBounds.sub_add_l h𝒩 hD hd (Or.inr hpj)
  have hspan : PowerlessAddition.addition_l ω e p.val d.val last.val := hpd ▸ F.add_graph_l p d
  obtain ⟨f₀, g, old₀, hf₀, hg, hslice, hLabels, hOrder, hLower, hOld₀, hgraph₀⟩ :=
    PowerlessBMSInitialSplit.exists_l hℳ hω hX hM hL hE hx hy hG hα hβ hspan
  have hzero : PowerlessBMSCopyState.state_l (he := he) (h₀ := h₀) (F := F)
      T t₁ t₂ t₃ c N H y p d α β g (zero_l 𝒩) := by
    simp only [PowerlessBMSCopyState.state_l, SecondOrderModel.mul_succ_l h𝒩,
      SecondOrderModel.mul_zero_l h𝒩, SecondOrderNumbers.zero_add_l h𝒩,
      SecondOrderModel.add_zero_l h𝒩, hpd]
    exact ⟨f₀, old₀, hf₀, hgraph₀, hOld₀⟩
  obtain ⟨f, old, hf, hgraph, hOld⟩ := PowerlessBMSCopyState.bounded_induction_l hℳ hω
    T t₁ t₂ t₃ c N H y p d α β g k hzero (fun copy hcopy hState => by
      obtain ⟨f, old, hf, hgraph, hOld⟩ := hState
      exact PowerlessBMSCopyStep.exists_l hℳ hω hX hW hP hI hS hTrim hZ hB hL hE hD hJ hAsc hM hO
        hx hmax hlast hparent hd hy hcopy ht hT hrow hc hc₀ hN hn hs hG hα hβ hOld hgraph hf hg
        hslice hLabels hOrder hLower hrowMax)
  obtain ⟨Λ, Θ, s, h, u, v, _, _, _, _, _, hU⟩ :=
    PowerlessBMSPrefixReflection.exists_l hℳ hω ht hT
      (Nat.le_trans (Nat.le_of_lt hrow) (Nat.le_succ H)) hc hc₀ hN hn hs hOld hgraph
      (PowerlessBMSCopyStep.span_l hℳ hω p d k) hf hg hLabels hOrder hLower
  have hwidth := SecondOrderProgramExpansionWidth.selected_width_l h𝒩 hX hW hP hL hD
    hx.1 hmax hparent hd hy
  exact ⟨α, u, (PowerlessFunction.value_mem_l hℳ hG.map_l hα).2,
    PowerlessBMSPrefixRepresentation.complete_l hU
      ((PowerlessBMSRepresentation.width_graph_l hL _ _).mpr hwidth)⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSExpansionDescent
