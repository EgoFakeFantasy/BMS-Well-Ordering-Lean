import BMSConstructibleBridge.PowerlessBMSPrefixRestoration

/-!
# 同一最终展开上的实际复制步

从当前前缀表示构造反射见证，再恢复固定原块，得到下一前缀表示。
两次拼接的长度都与实际内部复制下标对齐；调用者不再提供更新图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSCopyStep

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderModel (add_l mul_l succ_l)
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

/-- 复制根之间的差值就是固定坏块长度，内部加法图保留精确下标。 -/
theorem span_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    (p d copy : PowerlessArithmetic.num_l ω) :
    PowerlessAddition.addition_l ω e (add_l (ℳ := 𝒩) p (mul_l d copy)).val d.val
      (add_l (ℳ := 𝒩) p (mul_l d (succ_l copy))).val := by
  have h𝒩 := PowerlessArithmeticComprehension.models_l hℳ hω (he := he) (h₀ := h₀) (F := F)
  rw [SecondOrderModel.mul_succ_l h𝒩, ← SecondOrderNumbers.add_assoc_l h𝒩]
  exact F.add_graph_l (add_l (ℳ := 𝒩) p (mul_l d copy)) d

/-- 原边、原标签和有限反射预算实际产生下一复制状态的全部见证。 -/
theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
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
    {x last p d k maximal height y copy : PowerlessArithmetic.num_l ω}
    (hx : SecondOrderProgramRectangular.rectangular_l (ℳ := 𝒩) L E x (succ_l last) height)
    (hmax : SecondOrderPairing.relation_l (ℳ := 𝒩) W x (succ_l maximal))
    (hlast : SecondOrderPairing.relation_l (ℳ := 𝒩) I x last)
    (hparent : SecondOrderPairing.relation_l (ℳ := 𝒩) P
      (SecondOrderPairing.value_l (SecondOrderPairing.value_l x maximal) last) (succ_l p))
    (hd : SecondOrderPairing.relation_l (ℳ := 𝒩) D (SecondOrderPairing.value_l last p) d)
    (hy : SecondOrderPairing.relation_l (ℳ := 𝒩) X (SecondOrderPairing.value_l x k) y)
    (hcopy : SecondOrderOrder.lt_l (ℳ := 𝒩) copy k)
    {T t₁ t₂ t₃ c N n σ α β source f g old : carrier_l ℳ} {H rowMax : Nat}
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T) (hrow : rowMax < H)
    (hc : PowerlessGoodBoundary.code_l ω e T t₁ t₂ t₃ c N (level_m (H + 1) (H + 1)))
    (hc₀ : member_l ℳ c ω) (hN : member_l ℳ N ω)
    (hn : PowerlessNumeral.numeral_l e (level_m (H + 1) rowMax) n)
    (hs : PowerlessGoodBoundary.stable_l ω e T t₁ t₂ t₃ c N n α β)
    (hG : PowerlessBMSRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
      T t₁ t₂ t₃ c N H x (succ_l (ℳ := 𝒩) last) σ source)
    (hα : value_l source p.val α) (hβ : value_l source last.val β)
    (hOld : PowerlessBMSPrefixRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
      T t₁ t₂ t₃ c N H y (add_l (ℳ := 𝒩) p (mul_l d (succ_l copy))) β old)
    (hgraph : PowerlessConcatenation.graph_l ω e (add_l (ℳ := 𝒩) p (mul_l d copy)).val f g old)
    (hf : map_l f (add_l (ℳ := 𝒩) p (mul_l d copy)).val α) (hg : map_l g d.val β)
    (hslice : PowerlessShiftedRestriction.graph_l ω e p.val d.val source g)
    (hLabels : ∀ i a, value_l g i a → PowerlessCodedDiagram.good_l ω e T t₁ t₂ t₃ c N a)
    (hOrder : PowerlessConcatenation.increasing_l g)
    (hLower : ∀ i a, value_l g i a → member_l ℳ α a ∨ α = a)
    (hrowMax : PowerlessNumeral.numeral_l e rowMax maximal.val) :
    ∃ u v, map_l u (add_l (ℳ := 𝒩) p (mul_l d (succ_l copy))).val α ∧
      PowerlessConcatenation.graph_l ω e (add_l (ℳ := 𝒩) p (mul_l d (succ_l copy))).val u g v ∧
      PowerlessBMSPrefixRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
        T t₁ t₂ t₃ c N H y (add_l (ℳ := 𝒩) p (mul_l d (succ_l (succ_l copy)))) β v := by
  obtain ⟨Λ, Θ, s, h, u, v, _, hΘ, _, hΘ₀, hstep, hU⟩ :=
    PowerlessBMSPrefixReflection.exists_l hℳ hω ht hT
      (Nat.le_trans (Nat.le_of_lt hrow) (Nat.le_succ H)) hc hc₀ hN hn hs
      hOld hgraph (span_l hℳ hω p d copy) hf hg hLabels hOrder hLower
  have hsLength : s = (add_l (ℳ := 𝒩) p (mul_l d (succ_l (succ_l copy)))).val :=
    PowerlessAddition.unique_l hℳ hω he hstep.next_length_l
      (span_l hℳ hω (he := he) (h₀ := h₀) (F := F) p d (succ_l (ℳ := 𝒩) copy))
  subst s
  exact ⟨u, v, hstep.prefix_map_l, hstep.graph_l,
    PowerlessBMSPrefixRestoration.step_l hℳ hω hX hW hP hI hS hTrim hZ hB hL hE hD hJ hAsc hM hO
      hx hmax hlast hparent hd hy hcopy hG hα hβ hOld hgraph hf hg hslice hstep hU hrowMax hΘ hΘ₀⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSCopyStep
