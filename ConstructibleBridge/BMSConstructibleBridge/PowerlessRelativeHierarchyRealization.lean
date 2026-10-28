import BMSConstructibleBridge.PowerlessRelativeHierarchySemantics
import BMSConstructibleBridge.SecondOrderRelativeLevelMap
import BMSConstructibleBridge.SecondOrderOrdinalCases
import BMSConstructibleBridge.SecondOrderRelativeLevelZero
import BMSConstructibleBridge.SecondOrderRelativeLevelSuccessor
import BMSConstructibleBridge.SecondOrderRelativeLevelLimit

/-! # 实际层值函数满足纯集合历史公式

函数已经是商模型中的集合图。零、后继、极限方程通过任意编码的商唯一性
传输；因此得到纯对象历史，不要求整个商模型满足源 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeHierarchyRealization

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderQuotient (type_l mem_l mk_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private abbrev quotient_l (hℳ : Theory.Models ℳ theory_m) :=
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)

theorem step_l (hℳ : Theory.Models ℳ theory_m) {B : set_l ℳ}
    {hB : SecondOrderDomain.wf_l B (zero_l ℳ)} {A C : SecondOrderGraph.code_l ℳ}
    (hA : SetTheory.Structure.IsOrdinal (quotient_l hℳ) (mk_l hℳ A)) {f : type_l hℳ}
    (hMap : SecondOrderFunctionObjects.map_l hℳ f (mk_l hℳ A) (mk_l hℳ C))
    (hf : SecondOrderRelativeLevelRelation.graph_l hℳ B hB (mk_l hℳ A) (mk_l hℳ C) f)
    (x y : type_l hℳ) (hx : mem_l hℳ x (mk_l hℳ A))
    (hy : SecondOrderFunctionObjects.value_l hℳ f x y) :
    PowerlessRelativeHierarchySemantics.step_l hℳ (mk_l hℳ ⟨B, zero_l ℳ, hB⟩) f x y := by
  obtain ⟨α, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
  obtain ⟨Y, rfl⟩ := SecondOrderQuotient.surj_l hℳ y
  have hα : SetTheory.Structure.IsOrdinal (quotient_l hℳ) (mk_l hℳ α) := by
    apply SetTheory.Structure.IsOrdinal.mem hA
    exact hx
  have hY := (SecondOrderRelativeLevelRelation.quotient_code_l hℳ α Y).mp
    ((SecondOrderRelativeLevelRelation.value_iff_l hℳ hf _ _).mp hy).2.2
  rcases SecondOrderOrdinalCases.cases_l hℳ α hα with hEmpty | ⟨γ, hSucc⟩ | ⟨hNonempty, hNoMax⟩
  · refine Or.inl ⟨?_, (SecondOrderQuotient.eq_iff_l hℳ _ _).mpr (SecondOrderRelativeLevelZero.value_l hℳ hEmpty hY)⟩
    intro x hx
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    exact hEmpty X hx
  · have hγα : SecondOrderGraph.mem_l γ α := (hSucc γ).mpr (Or.inr (SecondOrderGraph.refl_l hℳ γ))
    have hγA : mem_l hℳ (mk_l hℳ γ) (mk_l hℳ A) :=
      hA.transitive (mk_l hℳ α) hx (mk_l hℳ γ) hγα
    obtain ⟨d, ⟨_, hd⟩, _⟩ := hMap.2 (mk_l hℳ γ) hγA
    obtain ⟨D, rfl⟩ := SecondOrderQuotient.surj_l hℳ d
    have hD := (SecondOrderRelativeLevelRelation.quotient_code_l hℳ γ D).mp
      ((SecondOrderRelativeLevelRelation.value_iff_l hℳ hf _ _).mp hd).2.2
    refine Or.inr (Or.inl ⟨mk_l hℳ γ, mk_l hℳ D, ?_, hd,
      SecondOrderRelativeLevelSuccessor.value_l hℳ hSucc hD hY⟩)
    intro x
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    exact (hSucc X).trans (or_congr Iff.rfl (SecondOrderQuotient.eq_iff_l hℳ X γ).symm)
  · refine Or.inr (Or.inr ⟨?_, ?_⟩)
    · refine ⟨?_, ?_⟩
      · obtain ⟨γ, hγ⟩ := hNonempty
        exact ⟨mk_l hℳ γ, hγ⟩
      · intro x hx
        obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
        obtain ⟨δ, hδ, hXδ⟩ := hNoMax X hx
        exact ⟨mk_l hℳ δ, hδ, hXδ⟩
    · intro x
      obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
      change SecondOrderGraph.mem_l X Y ↔ _
      rw [SecondOrderRelativeLevelLimit.value_l hℳ hNonempty hNoMax hY X]
      constructor
      · rintro ⟨γ, L, hγα, hL, hXL⟩
        have hγA : mem_l hℳ (mk_l hℳ γ) (mk_l hℳ A) :=
          hA.transitive (mk_l hℳ α) hx (mk_l hℳ γ) hγα
        obtain ⟨d, ⟨_, hd⟩, _⟩ := hMap.2 (mk_l hℳ γ) hγA
        have hLevelD := ((SecondOrderRelativeLevelRelation.value_iff_l hℳ hf _ _).mp hd).2.2
        have hLD := SecondOrderRelativeLevelRelation.quotient_unique_l hℳ
          ((SecondOrderRelativeLevelRelation.quotient_code_l hℳ γ L).mpr hL) hLevelD
        refine ⟨mk_l hℳ γ, d, hγα, hd, ?_⟩
        rw [← hLD]
        exact hXL
      · rintro ⟨γ, d, hγα, hd, hXd⟩
        obtain ⟨G₀, rfl⟩ := SecondOrderQuotient.surj_l hℳ γ
        obtain ⟨D, rfl⟩ := SecondOrderQuotient.surj_l hℳ d
        exact ⟨G₀, D, hγα, (SecondOrderRelativeLevelRelation.quotient_code_l hℳ G₀ D).mp
          ((SecondOrderRelativeLevelRelation.value_iff_l hℳ hf _ _).mp hd).2.2, hXd⟩

theorem history_l (hℳ : Theory.Models ℳ theory_m) {B : set_l ℳ}
    {hB : SecondOrderDomain.wf_l B (zero_l ℳ)} {A C : SecondOrderGraph.code_l ℳ}
    (hA : SetTheory.Structure.IsOrdinal (quotient_l hℳ) (mk_l hℳ A)) {f : type_l hℳ}
    (hMap : SecondOrderFunctionObjects.map_l hℳ f (mk_l hℳ A) (mk_l hℳ C))
    (hf : SecondOrderRelativeLevelRelation.graph_l hℳ B hB (mk_l hℳ A) (mk_l hℳ C) f) :
    PowerlessRelativeHierarchySemantics.history_l hℳ (mk_l hℳ ⟨B, zero_l ℳ, hB⟩)
      (mk_l hℳ A) f (mk_l hℳ C) :=
  ⟨hMap, fun x y h => step_l hℳ hA hMap hf x y h.1 h.2⟩

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (B : set_l ℳ)
    (hB : SecondOrderDomain.wf_l B (zero_l ℳ))
    (hBase : SecondOrderTransitiveSuperset.transitive_l ⟨B, zero_l ℳ, hB⟩)
    (A : SecondOrderGraph.code_l ℳ) (hA : SetTheory.Structure.IsOrdinal (quotient_l hℳ) (mk_l hℳ A)) :
    ∃ f r : type_l hℳ, PowerlessRelativeHierarchySemantics.history_l hℳ
      (mk_l hℳ ⟨B, zero_l ℳ, hB⟩) (mk_l hℳ A) f r := by
  obtain ⟨C, f, _, hMap, hf⟩ := SecondOrderRelativeLevelMap.exists_l hℳ B hB hBase A hA
  exact ⟨f, mk_l hℳ C, history_l hℳ hA hMap hf⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeHierarchyRealization
