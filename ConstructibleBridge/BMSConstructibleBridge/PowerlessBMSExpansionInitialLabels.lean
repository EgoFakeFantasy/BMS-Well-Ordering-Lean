import BMSConstructibleBridge.PowerlessBMSPrefixRepresentation
import BMSConstructibleBridge.SecondOrderProgramExpansionPrefix

/-!
# 最终展开上的初始前缀标签

直接限制原数组的标签图到除末列以外的全部原列，并把标签上界降到原末列标签。
真实展开保留这些列的祖先查询，故同一张限制图已经是最终展开的前缀表示。
本结论覆盖最大父行存在与不存在两支；新增副本仍须另行标号。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSExpansionInitialLabels

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

/-- 原非末列标签原样保留在最终展开上，且全部严格小于原末列标签。 -/
theorem initial_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    {X M L E : PowerlessArithmetic.set_l ω}
    (hX : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramExpansion.expand_m) X)
    (hM : graph_semantics_l (ℳ := 𝒩) (graph_m PowerlessBMSAncestor.program_m) M)
    (hL : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramLength.length_m) L)
    (hE : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramListLookup.lookup_m) E)
    {T t₁ t₂ t₃ c N σ β f : carrier_l ℳ} {H : Nat}
    {x y j height k : PowerlessArithmetic.num_l ω}
    (hx : SecondOrderProgramRectangular.rectangular_l (ℳ := 𝒩) L E x (F.succ_l j) height)
    (hy : SecondOrderPairing.relation_l (ℳ := 𝒩) X (SecondOrderPairing.value_l x k) y)
    (hG : PowerlessBMSRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
      T t₁ t₂ t₃ c N H x (F.succ_l j) σ f)
    (hβ : value_l f j.val β) :
    ∃ g, PowerlessBMSPrefixRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
        T t₁ t₂ t₃ c N H y j β g ∧
      ∀ i a, value_l g i a ↔ member_l ℳ i j.val ∧ value_l f i a := by
  have h𝒩 := PowerlessArithmeticComprehension.models_l hℳ hω (he := he) (h₀ := h₀) (F := F)
  have hj : subset_l j.val (F.succ_l j).val :=
    fun i hi => (F.succ_graph_l j i).mpr (Or.inl hi)
  obtain ⟨g, hg, hV⟩ := PowerlessBMSPrefixRepresentation.restrict_l hℳ
    (PowerlessBMSPrefixRepresentation.of_full_l hG) hj
  have hgβ : map_l g j.val β := PowerlessFunction.range_l hℳ hg.map_l (fun i a ha =>
    hG.order_l i j.val a β ((hV i a).mp ha).1 ((hV i a).mp ha).2 hβ)
  have hprefix : PowerlessBMSPrefixRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
      T t₁ t₂ t₃ c N H x j β g := ⟨hgβ, hg.labels_l, hg.order_l, hg.edge_l⟩
  refine ⟨g, PowerlessBMSPrefixRepresentation.transfer_l hℳ hprefix ?_, hV⟩
  intro r i t _ ht hancestor
  have ht₀ := (PowerlessArithmeticOrder.lt_l hℳ hω (he := he) (h₀ := h₀) (F := F) t j).mpr ht
  exact (PowerlessBMSAncestor.graph_l hM x r t i).mpr
    ((not_congr (SecondOrderProgramExpansionPrefix.member_l h𝒩 hX hM hL hE hx hy ht₀
      r i (SecondOrderModel.zero_l 𝒩))).mpr ((PowerlessBMSAncestor.graph_l hM y r t i).mp hancestor))

/-- 无最大父行的分支已经得到完整展开表示，且表示上界严格下降到原末列标签。 -/
theorem fallback_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    {X W M L E : PowerlessArithmetic.set_l ω}
    (hX : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramExpansion.expand_m) X)
    (hW : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramMaximalParentRow.maximal_m) W)
    (hM : graph_semantics_l (ℳ := 𝒩) (graph_m PowerlessBMSAncestor.program_m) M)
    (hL : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramLength.length_m) L)
    (hE : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramListLookup.lookup_m) E)
    {T t₁ t₂ t₃ c N σ β f : carrier_l ℳ} {H : Nat}
    {x y j height k : PowerlessArithmetic.num_l ω}
    (hx : SecondOrderProgramRectangular.rectangular_l (ℳ := 𝒩) L E x (F.succ_l j) height)
    (hw : SecondOrderPairing.relation_l (ℳ := 𝒩) W x (SecondOrderModel.zero_l 𝒩))
    (hy : SecondOrderPairing.relation_l (ℳ := 𝒩) X (SecondOrderPairing.value_l x k) y)
    (hG : PowerlessBMSRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
      T t₁ t₂ t₃ c N H x (F.succ_l j) σ f)
    (hβ : value_l f j.val β) :
    ∃ g, member_l ℳ β σ ∧
      PowerlessBMSRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
        T t₁ t₂ t₃ c N H y j β g ∧
      ∀ i a, value_l g i a ↔ member_l ℳ i j.val ∧ value_l f i a := by
  obtain ⟨g, hg, hV⟩ := initial_l hℳ hω hX hM hL hE hx hy hG hβ
  have h𝒩 := PowerlessArithmeticComprehension.models_l hℳ hω (he := he) (h₀ := h₀) (F := F)
  have hwidth := SecondOrderProgramExpansionFallback.expand_none_width_l
    h𝒩 (n := j) hX hW hL hx.1 hw hy
  exact ⟨g, (PowerlessFunction.value_mem_l hℳ hG.map_l hβ).2,
    PowerlessBMSPrefixRepresentation.complete_l hg
      ((PowerlessBMSRepresentation.width_graph_l hL y j).mpr hwidth), hV⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSExpansionInitialLabels
