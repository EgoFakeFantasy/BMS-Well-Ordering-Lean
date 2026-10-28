import BMSConstructibleBridge.PowerlessBMSPrefixReflection
import BMSConstructibleBridge.PowerlessBMSRelabelCrossing
import BMSConstructibleBridge.SecondOrderProgramExpansionPrefixToSuccessive

/-!
# 反射后恢复原块的实际前缀更新

固定同一个最终展开。已有 f+g 的前缀表示以及实际反射所得 f+h，
本节证明 f+h+g 是延长一块后的前缀表示。新出现的三类边分别使用
整个旧前缀的目标平移、跨副本原数组刻画及副本内对应，均来自原程序定理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSPrefixRestoration

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderModel (add_l mul_l succ_l zero_l)
open SecondOrderProgramSemantics
open PrimitiveProgram (graph_m)

set_option autoImplicit false

attribute [local implicit_reducible] PowerlessArithmetic.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  {ω e : carrier_l ℳ} {he : PowerlessNatural.zero_l e} {h₀ : member_l ℳ e ω}
  {F : PowerlessArithmetic.operations_l ω e}

local notation "𝒩" => PowerlessArithmetic.structure_l he h₀ F

/-- 非最后一个副本处，反射并恢复原块得到下一内部副本号的完整前缀表示。 -/
theorem step_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
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
    {x last p d k maximal height y copy total : PowerlessArithmetic.num_l ω}
    (hx : SecondOrderProgramRectangular.rectangular_l (ℳ := 𝒩) L E x (succ_l last) height)
    (hmax : SecondOrderPairing.relation_l (ℳ := 𝒩) W x (succ_l maximal))
    (hlast : SecondOrderPairing.relation_l (ℳ := 𝒩) I x last)
    (hparent : SecondOrderPairing.relation_l (ℳ := 𝒩) P
      (SecondOrderPairing.value_l (SecondOrderPairing.value_l x maximal) last) (succ_l p))
    (hd : SecondOrderPairing.relation_l (ℳ := 𝒩) D (SecondOrderPairing.value_l last p) d)
    (hy : SecondOrderPairing.relation_l (ℳ := 𝒩) X (SecondOrderPairing.value_l x k) y)
    (hcopy : SecondOrderOrder.lt_l (ℳ := 𝒩) copy k)
    {T t₁ t₂ t₃ c N σ α β source f g h old u v : carrier_l ℳ}
    {H rowMax : Nat} {Λ Θ : List (Nat × carrier_l ℳ)}
    (hG : PowerlessBMSRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
      T t₁ t₂ t₃ c N H x (succ_l (ℳ := 𝒩) last) σ source)
    (hα : value_l source p.val α) (hβ : value_l source last.val β)
    (hOld : PowerlessBMSPrefixRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
      T t₁ t₂ t₃ c N H y (add_l (ℳ := 𝒩) p (mul_l d (succ_l copy))) β old)
    (hgraph : PowerlessConcatenation.graph_l ω e (add_l (ℳ := 𝒩) p (mul_l d copy)).val f g old)
    (hf : map_l f (add_l (ℳ := 𝒩) p (mul_l d copy)).val α) (hg : map_l g d.val β)
    (hslice : PowerlessShiftedRestriction.graph_l ω e p.val d.val source g)
    (hstep : PowerlessRelabelAppend.step_l ω e T t₁ t₂ t₃ c N α β
      (add_l (ℳ := 𝒩) p (mul_l d copy)).val d.val
      (add_l (ℳ := 𝒩) p (mul_l d (succ_l copy))).val total.val f g h u v Λ Θ)
    (hU : PowerlessBMSPrefixRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
      T t₁ t₂ t₃ c N H y (add_l (ℳ := 𝒩) p (mul_l d (succ_l copy))) α u)
    (hrowMax : PowerlessNumeral.numeral_l e rowMax maximal.val)
    (hΘ : Θ.map Prod.fst = PowerlessRelabelLevels.levels_m (H + 1) rowMax)
    (hΘ₀ : ∀ tag ∈ Θ, PowerlessNumeral.numeral_l e tag.1 tag.2) :
    PowerlessBMSPrefixRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
      T t₁ t₂ t₃ c N H y total β v := by
  have h𝒩 := PowerlessArithmeticComprehension.models_l hℳ hω (he := he) (h₀ := h₀) (F := F)
  let r₀ := add_l (ℳ := 𝒩) p (mul_l d copy)
  let r₁ := add_l (ℳ := 𝒩) p (mul_l d (succ_l copy))
  have hcopy₀ := (SecondOrderNaturalGraph.lt_succ_l h𝒩 copy k).mpr (Or.inr hcopy)
  have hcopy₁ := (SecondOrderOrder.succ_iff_l h𝒩 copy k).mpr hcopy
  have hcopies := (SecondOrderNaturalGraph.lt_succ_l h𝒩 copy copy).mpr (Or.inl rfl)
  refine ⟨hstep.map_l, hstep.labels_l, hstep.order_l, ?_⟩
  intro rowIndex hrow row hr i t hit a b ha hb
  have haTotal := ha
  have hbTotal := hb
  rcases (hstep.graph_l i.val a).mp ha with ha | ⟨i₀, hi₀, ha⟩
  · rcases (hstep.graph_l t.val b).mp hb with hb | ⟨t₀, ht₀, hb⟩
    · exact hU.edge_l rowIndex hrow row hr i t hit a b ha hb
    · let zt : PowerlessArithmetic.num_l ω := ⟨t₀, PowerlessAdditionBounds.input_l hℳ ht₀⟩
      have ht : add_l (ℳ := 𝒩) r₁ zt = t :=
        Subtype.ext (PowerlessAddition.unique_l hℳ hω he (F.add_graph_l r₁ zt) ht₀)
      have htd := (PowerlessArithmeticOrder.lt_l hℳ hω (he := he) (h₀ := h₀) (F := F) zt d).mpr
        (PowerlessFunction.value_mem_l hℳ hg hb).1
      rcases (hstep.prefix_graph_l i.val a).mp ha with ha | ⟨i₀, hi₀, ha⟩
      · have hip := (PowerlessArithmeticOrder.lt_l hℳ hω (he := he) (h₀ := h₀) (F := F) i r₀).mpr
          (PowerlessFunction.value_mem_l hℳ hf ha).1
        have hagree := SecondOrderProgramExpansionPrefixToSuccessive.all_rows_l
          h𝒩 (row := row) hX hW hP hI hS hTrim hZ hB hL hE hD hJ hAsc hM hO
          hx hmax hlast hparent hd hy hcopy htd
        have hquery := (PowerlessBMSAncestor.graph_l hM y row t i).mp hit
        have hcurrent : PowerlessBMSAncestor.ancestor_l (he := he) (h₀ := h₀) (F := F)
            y row (add_l (ℳ := 𝒩) r₀ zt) i :=
          (PowerlessBMSAncestor.graph_l hM _ _ _ _).mpr
            ((hagree i hip).mpr (by simpa only [← ht] using hquery))
        exact hOld.edge_l rowIndex hrow row hr i (add_l (ℳ := 𝒩) r₀ zt) hcurrent a b
          ((hgraph i.val a).mpr (Or.inl ha))
          ((hgraph (add_l (ℳ := 𝒩) r₀ zt).val b).mpr (Or.inr ⟨t₀, F.add_graph_l r₀ zt, hb⟩))
      · let zi : PowerlessArithmetic.num_l ω := ⟨i₀, PowerlessAdditionBounds.input_l hℳ hi₀⟩
        have hi : add_l (ℳ := 𝒩) r₀ zi = i :=
          Subtype.ext (PowerlessAddition.unique_l hℳ hω he (F.add_graph_l r₀ zi) hi₀)
        have hid := (PowerlessArithmeticOrder.lt_l hℳ hω (he := he) (h₀ := h₀) (F := F) zi d).mpr
          (PowerlessFunction.value_mem_l hℳ hstep.image_map_l ha).1
        have hcross : PowerlessBMSAncestor.ancestor_l (he := he) (h₀ := h₀) (F := F)
            y row (add_l (ℳ := 𝒩) r₁ zt) (add_l (ℳ := 𝒩) r₀ zi) := by
          simpa only [hi, ht] using hit
        have hleft : value_l v (add_l (ℳ := 𝒩) r₀ zi).val a := by simpa only [hi] using haTotal
        have hright : value_l v (add_l (ℳ := 𝒩) r₁ zt).val b := by simpa only [ht] using hbTotal
        exact PowerlessBMSRelabelCrossing.edge_l hℳ hω hX hW hP hI hS hTrim hZ hB hL hE hD hJ hAsc hM hO
          hx hmax hlast hparent hd hy hcopies hcopy₁ hid htd hG hα hβ hg hslice hstep
          hrow hr hrowMax hΘ hΘ₀ hcross hleft hright
  · rcases (hstep.graph_l t.val b).mp hb with hb | ⟨t₀, ht₀, hb⟩
    · have hip : member_l ℳ i.val r₁.val := PowerlessNaturalOrder.member_transitive_l hℳ hω r₁.val r₁.property
        t.val i.val (PowerlessFunction.value_mem_l hℳ hU.map_l hb).1 (PowerlessBMSAncestor.bound_l hℳ hω hit)
      rcases PowerlessAdditionBounds.lower_l hℳ hω he r₁.property hi₀ with hpi | hpi
      · exact (PowerlessNatural.asymmetry_l hℳ hip hpi).elim
      · have hii : member_l ℳ i.val i.val := hpi ▸ hip
        exact (PowerlessNatural.asymmetry_l hℳ hii hii).elim
    · let zi : PowerlessArithmetic.num_l ω := ⟨i₀, PowerlessAdditionBounds.input_l hℳ hi₀⟩
      let zt : PowerlessArithmetic.num_l ω := ⟨t₀, PowerlessAdditionBounds.input_l hℳ ht₀⟩
      have hi : add_l (ℳ := 𝒩) r₁ zi = i :=
        Subtype.ext (PowerlessAddition.unique_l hℳ hω he (F.add_graph_l r₁ zi) hi₀)
      have ht : add_l (ℳ := 𝒩) r₁ zt = t :=
        Subtype.ext (PowerlessAddition.unique_l hℳ hω he (F.add_graph_l r₁ zt) ht₀)
      have hid := (PowerlessArithmeticOrder.lt_l hℳ hω (he := he) (h₀ := h₀) (F := F) zi d).mpr
        (PowerlessFunction.value_mem_l hℳ hg ha).1
      have htd := (PowerlessArithmeticOrder.lt_l hℳ hω (he := he) (h₀ := h₀) (F := F) zt d).mpr
        (PowerlessFunction.value_mem_l hℳ hg hb).1
      have hinside := SecondOrderProgramExpansionInsideCopiesAllRows.member_congr_l
        h𝒩 (row := row) hX hW hP hI hB hL hE hD hJ hM hx hmax hlast hparent hd hy
        hcopy₀ hcopy₁ hid htd
      have hcurrent : PowerlessBMSAncestor.ancestor_l (he := he) (h₀ := h₀) (F := F)
          y row (add_l (ℳ := 𝒩) r₀ zt) (add_l (ℳ := 𝒩) r₀ zi) := by
        apply (PowerlessBMSAncestor.graph_l hM _ _ _ _).mpr
        have hnext : PowerlessBMSAncestor.ancestor_l (he := he) (h₀ := h₀) (F := F)
            y row (add_l (ℳ := 𝒩) r₁ zt) (add_l (ℳ := 𝒩) r₁ zi) := by
          simpa only [hi, ht] using hit
        have hnextQuery := (PowerlessBMSAncestor.graph_l hM _ _ _ _).mp hnext
        simpa only [r₀, SecondOrderNumbers.add_assoc_l h𝒩] using
          hinside.mpr (by simpa only [r₁, SecondOrderNumbers.add_assoc_l h𝒩] using hnextQuery)
      exact hOld.edge_l rowIndex hrow row hr (add_l (ℳ := 𝒩) r₀ zi) (add_l (ℳ := 𝒩) r₀ zt)
        hcurrent a b
        ((hgraph (add_l (ℳ := 𝒩) r₀ zi).val a).mpr (Or.inr ⟨i₀, F.add_graph_l r₀ zi, ha⟩))
        ((hgraph (add_l (ℳ := 𝒩) r₀ zt).val b).mpr (Or.inr ⟨t₀, F.add_graph_l r₀ zt, hb⟩))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSPrefixRestoration
