import BMSConstructibleBridge.PowerlessBMSExpansionDescent
import BMSConstructibleBridge.SecondOrderProgramFallbackDescent
import BMSConstructibleBridge.SecondOrderNumeralBounds

/-!
# 真实严格展开的统一表示下降

最大父行、父列及坏块长均由原程序实际取得。有父分支用内部复制归纳，
无父分支用原标签限制。空宽度只可能不严格变化，故不形成下降步。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSStrictDescent

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderModel (succ_l zero_l)
open SecondOrderProgramSemantics SecondOrderProgramTotality SecondOrderProgramArithmetic
open PrimitiveProgram (graph_m)
open PowerlessRelabelLevels (level_m)

set_option autoImplicit false

attribute [local implicit_reducible] PowerlessArithmetic.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  {ω e : carrier_l ℳ} {he : PowerlessNatural.zero_l e} {h₀ : member_l ℳ e ω}
  {F : PowerlessArithmetic.operations_l ω e}

local notation "𝒩" => PowerlessArithmetic.structure_l he h₀ F

/-- 任意真实严格展开都使同一预算下的完整表示上界严格下降。 -/
theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    {X L E : PowerlessArithmetic.set_l ω}
    (hX : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramExpansion.expand_m) X)
    (hL : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramLength.length_m) L)
    (hE : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramListLookup.lookup_m) E)
    {x q k height y : PowerlessArithmetic.num_l ω}
    (hx : SecondOrderProgramRectangular.rectangular_l (ℳ := 𝒩) L E x q height)
    (hy : SecondOrderPairing.relation_l (ℳ := 𝒩) X (SecondOrderPairing.value_l x k) y)
    (hne : y ≠ x) {T t₁ t₂ t₃ c N σ source bound : carrier_l ℳ} {H : Nat}
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (hc : PowerlessGoodBoundary.code_l ω e T t₁ t₂ t₃ c N (level_m (H + 1) (H + 1)))
    (hc₀ : member_l ℳ c ω) (hN : member_l ℳ N ω)
    (hbound : PowerlessNumeral.numeral_l e H bound) (hheight : subset_l height.val bound)
    (hG : PowerlessBMSRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
      T t₁ t₂ t₃ c N H x q σ source) :
    ∃ r : PowerlessArithmetic.num_l ω, ∃ α f, member_l ℳ α σ ∧
      PowerlessBMSRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
        T t₁ t₂ t₃ c N H y r α f := by
  have h𝒩 := PowerlessArithmeticComprehension.models_l hℳ hω (he := he) (h₀ := h₀) (F := F)
  obtain ⟨W, hWf, hW⟩ := graph_total_l h𝒩 SecondOrderProgramMaximalParentRow.maximal_m
  obtain ⟨M, _, hM⟩ := graph_total_l h𝒩 PowerlessBMSAncestor.program_m
  obtain ⟨z, hz, _⟩ := hWf x
  rcases SecondOrderModel.predecessor_l h𝒩 z with rfl | ⟨maximal, rfl⟩
  · rcases SecondOrderModel.predecessor_l h𝒩 q with rfl | ⟨last, rfl⟩
    · obtain ⟨r, hr, _⟩ := function_of_semantics_l h𝒩 SecondOrderProgramLength.length_m hL y
      exact (SecondOrderNumeralBounds.not_lt_zero_l h𝒩 r
        (SecondOrderProgramFallbackDescent.width_lt_l h𝒩 hX hW hL hx.1 hr hz hy hne)).elim
    · obtain ⟨β, ⟨_, hβ⟩, _⟩ := hG.map_l.2 last.val ((F.succ_graph_l last last.val).mpr (Or.inr rfl))
      obtain ⟨f, hβσ, hf, _⟩ :=
        PowerlessBMSExpansionInitialLabels.fallback_l hℳ hω hX hW hM hL hE hx hz hy hG hβ
      exact ⟨last, β, f, hβσ, hf⟩
  · obtain ⟨P, _, hP⟩ := graph_total_l h𝒩 SecondOrderProgramUniformParent.parent_m
    obtain ⟨I, _, hI⟩ := graph_total_l h𝒩 SecondOrderProgramMaximalParentRow.last_index_m
    obtain ⟨D, hDf, hD⟩ := graph_total_l h𝒩 SecondOrderProgramSubtraction.sub_m
    obtain ⟨last, p, hwidth, hparent, _⟩ :=
      SecondOrderProgramMaximalParentSelection.width_parent_l h𝒩 hW hP hL hz
    have hq := SecondOrderProgramSemantics.function_value_unique_l
      (function_of_semantics_l h𝒩 SecondOrderProgramLength.length_m hL) hx.1 hwidth
    subst q
    obtain ⟨Q, _, hQ⟩ := graph_total_l h𝒩 SecondOrderProgramListCode.pred_m
    have hlast := (SecondOrderProgramExpansionFallback.index_rel_l h𝒩 hI hL hQ hwidth last).mpr
      ((SecondOrderProgramListCode.pred_succ_l h𝒩 hQ last last).mpr rfl)
    obtain ⟨d, hd, _⟩ := hDf (SecondOrderPairing.value_l last p)
    obtain ⟨S, _, hS⟩ := graph_total_l h𝒩 SecondOrderProgramExpansionSuccess.success_m
    obtain ⟨Trim, _, hTrim⟩ := graph_total_l h𝒩 SecondOrderProgramTrimArray.trim_m
    obtain ⟨Z, _, hZ⟩ := graph_total_l h𝒩 SecondOrderProgramTrimHeight.trim_m
    obtain ⟨B, _, hB⟩ := graph_total_l h𝒩 SecondOrderProgramExpansionSuccess.bad_m
    obtain ⟨J, _, hJ⟩ := graph_total_l h𝒩 SecondOrderProgramEntry.entry_m
    obtain ⟨Asc, _, hAsc⟩ := graph_total_l h𝒩 SecondOrderProgramAscending.ascending_m
    obtain ⟨O, _, hO⟩ := graph_total_l h𝒩 SecondOrderProgramOptionalLookup.optional_m
    obtain ⟨α, f, hασ, hf⟩ := PowerlessBMSExpansionDescent.selected_l hℳ hω
      hX hW hP hI hS hTrim hZ hB hL hE hD hJ hAsc hM hO
      hx hz hlast hparent hd hy ht hT hc hc₀ hN hbound hheight hG
    exact ⟨_, α, f, hασ, hf⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSStrictDescent
