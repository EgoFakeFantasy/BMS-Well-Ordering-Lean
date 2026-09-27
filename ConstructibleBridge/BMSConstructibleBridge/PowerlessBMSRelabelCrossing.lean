import BMSConstructibleBridge.PowerlessBMSRepresentation
import BMSConstructibleBridge.PowerlessRelabelCoordinates
import BMSConstructibleBridge.PowerlessShiftedRestriction
import BMSConstructibleBridge.PowerlessNumeralOrder
import BMSConstructibleBridge.SecondOrderProgramExpansionCrossingSource

/-!
# 实际展开跨副本边的反射标签保持

跨副本祖先刻画给出原左列通向末列、原父列通向右列的两条源边。
原表示把两边变成稳定边，同一个反射见证再把左端降到父列标签之下，
最后由传递性接回恢复块。这里真正消费原展开算法，不把所需源边作为额外假设。
反射图及具名低层仍取自实际重标号步骤；本模块尚不装配全部内部迭代。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSRelabelCrossing

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

/-- 反射块到恢复块的真实祖先边，在同一拼接标签图上满足对应的低层稳定性。 -/
theorem edge_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
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
    {x last p d k maximal height y row earlier later i q : PowerlessArithmetic.num_l ω}
    (hx : SecondOrderProgramRectangular.rectangular_l (ℳ := 𝒩) L E x (succ_l last) height)
    (hmax : SecondOrderPairing.relation_l (ℳ := 𝒩) W x (succ_l maximal))
    (hlast : SecondOrderPairing.relation_l (ℳ := 𝒩) I x last)
    (hparent : SecondOrderPairing.relation_l (ℳ := 𝒩) P
      (SecondOrderPairing.value_l (SecondOrderPairing.value_l x maximal) last) (succ_l p))
    (hd : SecondOrderPairing.relation_l (ℳ := 𝒩) D (SecondOrderPairing.value_l last p) d)
    (hy : SecondOrderPairing.relation_l (ℳ := 𝒩) X (SecondOrderPairing.value_l x k) y)
    (hcopies : SecondOrderOrder.lt_l (ℳ := 𝒩) earlier later)
    (hlater : SecondOrderOrder.lt_l (ℳ := 𝒩) later (succ_l k))
    (hi : SecondOrderOrder.lt_l (ℳ := 𝒩) i d) (hq : SecondOrderOrder.lt_l (ℳ := 𝒩) q d)
    {T t₁ t₂ t₃ c N σ α β source old g h u v total A a₁ b₁ : carrier_l ℳ}
    {H rowIndex rowMax : Nat} {Λ Θ : List (Nat × carrier_l ℳ)}
    (hG : PowerlessBMSRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
      T t₁ t₂ t₃ c N H x (succ_l (ℳ := 𝒩) last) σ source)
    (hα : value_l source p.val α) (hβ : value_l source last.val β)
    (hg : map_l g d.val A)
    (hslice : PowerlessShiftedRestriction.graph_l ω e p.val d.val source g)
    (hstep : PowerlessRelabelAppend.step_l ω e T t₁ t₂ t₃ c N α β
      (add_l (ℳ := 𝒩) p (mul_l d earlier)).val d.val
      (add_l (ℳ := 𝒩) p (mul_l d later)).val total old g h u v Λ Θ)
    (hrow : rowIndex < H) (hr : PowerlessNumeral.numeral_l e rowIndex row.val)
    (hrowMax : PowerlessNumeral.numeral_l e rowMax maximal.val)
    (hΘ : Θ.map Prod.fst = PowerlessRelabelLevels.levels_m (H + 1) rowMax)
    (hΘ₀ : ∀ tag ∈ Θ, PowerlessNumeral.numeral_l e tag.1 tag.2)
    (hancestor : PowerlessBMSAncestor.ancestor_l (he := he) (h₀ := h₀) (F := F) y row
      (add_l (ℳ := 𝒩) (add_l p (mul_l d later)) q)
      (add_l (ℳ := 𝒩) (add_l p (mul_l d earlier)) i))
    (ha₁ : value_l v (add_l (ℳ := 𝒩) (add_l p (mul_l d earlier)) i).val a₁)
    (hb₁ : value_l v (add_l (ℳ := 𝒩) (add_l p (mul_l d later)) q).val b₁) :
    ∃ m, PowerlessNumeral.numeral_l e (PowerlessRelabelLevels.level_m (H + 1) rowIndex) m ∧
      PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ m a₁ b₁ := by
  have h𝒩 := PowerlessArithmeticComprehension.models_l hℳ hω (he := he) (h₀ := h₀) (F := F)
  have hquery := (PowerlessBMSAncestor.graph_l hM _ _ _ _).mp hancestor
  have hsource := (SecondOrderProgramExpansionCrossingSource.source_iff_l
    h𝒩 (row := row) hX hW hP hI hS hTrim hZ hB hL hE hD hJ hAsc hM hO
    hx hmax hlast hparent hd hy hcopies hlater hi hq).mp
      (by simpa only [SecondOrderNumbers.add_assoc_l h𝒩] using hquery)
  have hrowBelow : rowIndex < rowMax := (PowerlessNumeralOrder.member_iff_l hℳ hr hrowMax).mp
    ((PowerlessArithmeticOrder.lt_l hℳ hω (he := he) (h₀ := h₀) (F := F) row maximal).mp hsource.1)
  have hlevel : PowerlessRelabelLevels.level_m (H + 1) rowIndex ∈ Θ.map Prod.fst :=
    hΘ.symm ▸ PowerlessRelabelLevels.mem_m (H + 1) hrowBelow
  obtain ⟨tag, htag, htagIndex⟩ := List.mem_map.mp hlevel
  have htag₀ : PowerlessNumeral.numeral_l e (PowerlessRelabelLevels.level_m (H + 1) rowIndex) tag.2 :=
    htagIndex ▸ hΘ₀ tag htag
  refine ⟨tag.2, htag₀, ?_⟩
  have hedge (a b : PowerlessArithmetic.num_l ω)
      (hab : PowerlessBMSAncestor.ancestor_l (he := he) (h₀ := h₀) (F := F) x row b a)
      (α₀ β₀ : carrier_l ℳ) (ha : value_l source a.val α₀) (hb : value_l source b.val β₀) :
      PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ tag.2 α₀ β₀ := by
    obtain ⟨m, hm, hs⟩ := hG.edge_l rowIndex hrow row hr a b hab α₀ β₀ ha hb
    exact PowerlessNumeral.unique_l hℳ hm htag₀ ▸ hs
  have hid := (PowerlessArithmeticOrder.lt_l hℳ hω (he := he) (h₀ := h₀) (F := F) i d).mp hi
  have hqd := (PowerlessArithmeticOrder.lt_l hℳ hω (he := he) (h₀ := h₀) (F := F) q d).mp hq
  obtain ⟨a, ⟨_, ha⟩, _⟩ := hg.2 i.val hid
  obtain ⟨b, ⟨_, hb⟩, _⟩ := hg.2 q.val hqd
  have haSource : value_l source (add_l (ℳ := 𝒩) p i).val a :=
    (PowerlessShiftedRestriction.at_l hℳ hω he hslice hid (F.add_graph_l p i)).mp ha
  have hbSource : value_l source (add_l (ℳ := 𝒩) p q).val b :=
    (PowerlessShiftedRestriction.at_l hℳ hω he hslice hqd (F.add_graph_l p q)).mp hb
  have htop := hedge (add_l (ℳ := 𝒩) p i) last
    ((PowerlessBMSAncestor.graph_l hM _ _ _ _).mpr hsource.2.1) a β haSource hβ
  have hbase : b = α ∨ PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ tag.2 α b := by
    rcases hsource.2.2 with hzero | hfirst
    · have hb₀ : value_l source p.val b := by
        simpa only [hzero, SecondOrderModel.add_zero_l h𝒩] using hbSource
      exact Or.inl (PowerlessFunction.value_unique_l hℳ hG.map_l hb₀ hα)
    · exact Or.inr (hedge p (add_l (ℳ := 𝒩) p q)
        ((PowerlessBMSAncestor.graph_l hM _ _ _ _).mpr hfirst) α b hα hbSource)
  exact PowerlessRelabelCoordinates.cross_l hℳ hstep hω hg htag ha hb htop hbase
    (F.add_graph_l (add_l (ℳ := 𝒩) p (mul_l d earlier)) i)
    (F.add_graph_l (add_l (ℳ := 𝒩) p (mul_l d later)) q) ha₁ hb₁

#print axioms edge_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSRelabelCrossing
