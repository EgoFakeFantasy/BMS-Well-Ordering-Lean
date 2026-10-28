import BMSConstructibleBridge.PowerlessBMSRepresentation
import BMSConstructibleBridge.PowerlessShiftedRestriction

/-!
# 从原表示实际截取坏块标签

区间 [p,j) 用局部域 d 重新编号，其中 p+d=j。标签严格小于原末列标签 β，
并不小于原父列标签 α；好标签和严格递增性均从原表示继承。
这是反射重标号输入块的真实集合构造，不另行假设一张具有这些性质的标签图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSLabelBlock

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] PowerlessArithmetic.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  {ω e : carrier_l ℳ} {he : PowerlessNatural.zero_l e} {h₀ : member_l ℳ e ω}
  {F : PowerlessArithmetic.operations_l ω e}

/-- 原父列到末列之前的实际标签块满足反射步骤需要的域、界、标签及顺序条件。 -/
theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    {T t₁ t₂ t₃ c N σ α β f : carrier_l ℳ} {H : Nat}
    {x j p d : PowerlessArithmetic.num_l ω}
    (hG : PowerlessBMSRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
      T t₁ t₂ t₃ c N H x (F.succ_l j) σ f)
    (hα : value_l f p.val α) (hβ : value_l f j.val β)
    (hd : PowerlessAddition.addition_l ω e p.val d.val j.val) :
    ∃ g, map_l g d.val β ∧ PowerlessShiftedRestriction.graph_l ω e p.val d.val f g ∧
      (∀ i a, value_l g i a → PowerlessCodedDiagram.good_l ω e T t₁ t₂ t₃ c N a) ∧
      PowerlessConcatenation.increasing_l g ∧
      ∀ i a, value_l g i a → member_l ℳ α a ∨ α = a := by
  have hj : subset_l j.val (F.succ_l j).val :=
    fun i hi => (F.succ_graph_l j i).mpr (Or.inl hi)
  obtain ⟨g, hg, hV⟩ := PowerlessShiftedRestriction.exists_l hℳ hω he p.property d.property hd hj hG.map_l
  have hgβ : map_l g d.val β := PowerlessFunction.range_l hℳ hg (fun i a ha => by
    obtain ⟨hi, t, ht, ha⟩ := (hV i a).mp ha
    exact hG.order_l t j.val a β (PowerlessAdditionOrder.monotone_l hℳ hω he hi ht hd) ha hβ)
  refine ⟨g, hgβ, hV, ?_, PowerlessShiftedRestriction.order_l hℳ hω he hV hG.order_l, ?_⟩
  · intro i a ha
    obtain ⟨_, t, _, ha⟩ := (hV i a).mp ha
    exact hG.labels_l t a ha
  · intro i a ha
    obtain ⟨_, t, ht, ha⟩ := (hV i a).mp ha
    rcases PowerlessAdditionBounds.lower_l hℳ hω he p.property ht with hpt | hpt
    · exact Or.inl (hG.order_l p.val t α a hpt hα ha)
    · exact Or.inr (PowerlessFunction.value_unique_l hℳ hG.map_l hα (hpt.symm ▸ ha))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSLabelBlock
