import BMSConstructibleBridge.PowerlessBMSExpansionInitialLabels
import BMSConstructibleBridge.PowerlessBMSLabelBlock

/-!
# 内部标签迭代的实际初始拆分

从原表示构造父列之前的图 f 与原坏块图 g，并实际拼接为 f+g。
其逐点值仍等于原非末列标签，故它是同一最终展开上的初始前缀表示。
前缀标签低于 α，坏块标签位于 [α,β)，不预设迭代初始状态存在。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSInitialSplit

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

/-- 初始前缀、固定原块和它们在最终展开上的拼接表示都由原表示实际构造。 -/
theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    {X M L E : PowerlessArithmetic.set_l ω}
    (hX : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramExpansion.expand_m) X)
    (hM : graph_semantics_l (ℳ := 𝒩) (graph_m PowerlessBMSAncestor.program_m) M)
    (hL : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramLength.length_m) L)
    (hE : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramListLookup.lookup_m) E)
    {T t₁ t₂ t₃ c N σ α β source : carrier_l ℳ} {H : Nat}
    {x y j p d height k : PowerlessArithmetic.num_l ω}
    (hx : SecondOrderProgramRectangular.rectangular_l (ℳ := 𝒩) L E x (F.succ_l j) height)
    (hy : SecondOrderPairing.relation_l (ℳ := 𝒩) X (SecondOrderPairing.value_l x k) y)
    (hG : PowerlessBMSRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
      T t₁ t₂ t₃ c N H x (F.succ_l j) σ source)
    (hα : value_l source p.val α) (hβ : value_l source j.val β)
    (hspan : PowerlessAddition.addition_l ω e p.val d.val j.val) :
    ∃ f g old, map_l f p.val α ∧ map_l g d.val β ∧
      PowerlessShiftedRestriction.graph_l ω e p.val d.val source g ∧
      (∀ i a, value_l g i a → PowerlessCodedDiagram.good_l ω e T t₁ t₂ t₃ c N a) ∧
      PowerlessConcatenation.increasing_l g ∧
      (∀ i a, value_l g i a → member_l ℳ α a ∨ α = a) ∧
      PowerlessBMSPrefixRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
        T t₁ t₂ t₃ c N H y j β old ∧
      PowerlessConcatenation.graph_l ω e p.val f g old := by
  have hpj : subset_l p.val j.val := by
    intro i hi
    rcases PowerlessAdditionBounds.lower_l hℳ hω he p.property hspan with hpj | hpj
    · exact PowerlessNaturalOrder.member_transitive_l hℳ hω j.val j.property p.val i hpj hi
    · exact hpj ▸ hi
  have hp : subset_l p.val (F.succ_l j).val :=
    fun i hi => (F.succ_graph_l j i).mpr (Or.inl (hpj i hi))
  obtain ⟨f, hf, hF⟩ := PowerlessRestriction.exists_l hℳ hG.map_l hp
  have hfα : map_l f p.val α := PowerlessFunction.range_l hℳ hf (fun i a ha =>
    hG.order_l i p.val a α ((hF i a).mp ha).1 ((hF i a).mp ha).2 hα)
  have hfβ : map_l f p.val β := PowerlessFunction.range_l hℳ hf (fun i a ha =>
    hG.order_l i j.val a β (hpj i ((hF i a).mp ha).1) ((hF i a).mp ha).2 hβ)
  obtain ⟨g, hg, hSlice, hLabels, hOrder, hLower⟩ := PowerlessBMSLabelBlock.exists_l hℳ hω hG hα hβ hspan
  obtain ⟨old, hOld, hgraph⟩ := PowerlessConcatenation.exists_l hℳ hω he p.property d.property hspan hfβ hg
  obtain ⟨initial, hInitial, hV⟩ := PowerlessBMSExpansionInitialLabels.initial_l hℳ hω hX hM hL hE hx hy hG hβ
  have hsame (i a : carrier_l ℳ) (ha : value_l old i a) : value_l initial i a := by
    apply (hV i a).mpr
    refine ⟨(PowerlessFunction.value_mem_l hℳ hOld ha).1, ?_⟩
    rcases (hgraph i a).mp ha with ha | ⟨z, hz, ha⟩
    · exact ((hF i a).mp ha).2
    · obtain ⟨_, t, ht, ha⟩ := (hSlice z a).mp ha
      exact (PowerlessAddition.unique_l hℳ hω he ht hz) ▸ ha
  refine ⟨f, g, old, hfα, hg, hSlice, hLabels, hOrder, hLower, ?_, hgraph⟩
  refine ⟨hOld, fun i a ha => hInitial.labels_l i a (hsame i a ha), ?_, ?_⟩
  · exact fun i t a b hit ha hb => hInitial.order_l i t a b hit (hsame i a ha) (hsame t b hb)
  · exact fun j hj row hr i t hit a b ha hb =>
      hInitial.edge_l j hj row hr i t hit a b (hsame i.val a ha) (hsame t.val b hb)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSInitialSplit
