import BMSConstructibleBridge.SecondOrderRelativeLevelMonotonicity

/-! # 非零极限阶段的精确并集方程

极限条件直接表述为非空且每个成员上方还有成员。与母序数的规范前驱图
核对后读取实际历史的极限分支；反向包含由任意母历史的层值唯一性传输。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeLevelLimit

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem value_l (hℳ : Theory.Models ℳ theory_m) {B : set_l ℳ}
    {hB : SecondOrderDomain.wf_l B (zero_l ℳ)} {β C : SecondOrderGraph.code_l ℳ}
    (hNonempty : ∃ γ : SecondOrderGraph.code_l ℳ, SecondOrderGraph.mem_l γ β)
    (hNoMax : ∀ γ : SecondOrderGraph.code_l ℳ, SecondOrderGraph.mem_l γ β →
      ∃ δ : SecondOrderGraph.code_l ℳ, SecondOrderGraph.mem_l δ β ∧ SecondOrderGraph.mem_l γ δ)
    (hC : SecondOrderRelativeLevel.spec_l hℳ B hB β C) (X : SecondOrderGraph.code_l ℳ) :
    SecondOrderGraph.mem_l X C ↔ ∃ α Y : SecondOrderGraph.code_l ℳ,
      SecondOrderGraph.mem_l α β ∧ SecondOrderRelativeLevel.spec_l hℳ B hB α Y ∧ SecondOrderGraph.mem_l X Y := by
  obtain ⟨A, hA, Q, D, R, S, m, W, hP, hS, hm, hβm, hWm, hCW⟩ := hC
  let M := SecondOrderRootCorrespondence.member_code_l hℳ A hP m hm
  have hβM : SecondOrderGraph.eq_l β M := hβm
  have hTrans := SecondOrderRootOrdinalRelation.transitive_l hℳ A hA
    hP.equality hP.representatives hP.predecessors
  have hIrrefl := SecondOrderRootOrdinalRelation.irreflexive_l hℳ A
    hP.equality hP.representatives hP.predecessors
  have hAsymm : ∀ i j, relation_l R i j → ¬relation_l R j i :=
    fun i j hij hji => hIrrefl i (hTrans i j i hij hji)
  have hLimit : SecondOrderRelativeHierarchyStep.limit_l R m := by
    constructor
    · intro hMin
      obtain ⟨γ, hγ⟩ := hNonempty
      have hγM := (SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ γ) hβM).mp hγ
      obtain ⟨i, _, him, _⟩ := SecondOrderRootCorrespondence.predecessor_exists_l hℳ A hP
        (SecondOrderOrdinalHistoryCoherence.ordinal_transitive_l hℳ A hA) γ hm hγM
      exact hMin i him
    · rintro ⟨k, hk⟩
      have hkd := ((hP.predecessors k m).mp hk.1).1
      let K := SecondOrderRootCorrespondence.member_code_l hℳ A hP k hkd
      have hKM := (SecondOrderRootCorrespondence.edge_iff_l hℳ A hP hkd hm).mp hk.1
      have hKβ := (SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ K) hβM).mpr hKM
      obtain ⟨δ, hδ, hKδ⟩ := hNoMax K hKβ
      have hδM := (SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ δ) hβM).mp hδ
      obtain ⟨i, hi, him, hδi⟩ := SecondOrderRootCorrespondence.predecessor_exists_l hℳ A hP
        (SecondOrderOrdinalHistoryCoherence.ordinal_transitive_l hℳ A hA) δ hm hδM
      have hki : relation_l R k i := (SecondOrderRootCorrespondence.edge_iff_l hℳ A hP hkd hi).mpr
        ((SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ K) hδi).mp hKδ)
      rcases hk.2 i him with h | hik
      · subst i
        exact hIrrefl k hki
      · exact hAsymm k i hki hik
  obtain ⟨G, P, hUnion⟩ : SecondOrderPredecessorUnion.output_l R S m W := by
    rcases hS.history m W hWm with ⟨hMin, _⟩ | ⟨k, _, hk, _, _⟩ | ⟨_, hUnion⟩
    · exact False.elim (hLimit.1 hMin)
    · exact False.elim (hLimit.2 ⟨k, hk⟩)
    · exact hUnion
  have hRows : SecondOrderPredecessorUnionSemantics.rows_wf_l R S m :=
    fun i _ V hV => hS.wellFounded i V hV
  let U : SecondOrderGraph.code_l ℳ := ⟨W, zero_l ℳ, hS.wellFounded m W hWm⟩
  have hEq : SecondOrderGraph.eq_l C U := hCW
  rw [SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ X) hEq]
  change SecondOrderGraph.mem_l X (SecondOrderPredecessorUnionSemantics.code_l hℳ hUnion hRows) ↔ _
  rw [SecondOrderPredecessorUnionSemantics.mem_l hℳ hUnion hRows X]
  constructor
  · rintro ⟨i, Y, him, hY, hRoot, hXY⟩
    have hi := ((hP.predecessors i m).mp him).1
    let I := SecondOrderRootCorrespondence.member_code_l hℳ A hP i hi
    have hIβ := (SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ I) hβM).mpr
      ((SecondOrderRootCorrespondence.edge_iff_l hℳ A hP hi hm).mp him)
    refine ⟨I, Y, hIβ, ?_, hXY⟩
    refine ⟨A, hA, Q, D, R, S, i, Y.real, hP, hS, hi,
      SecondOrderBisimulation.refl_l hℳ A.real i, hY, ?_⟩
    rw [hRoot]
    exact SecondOrderBisimulation.refl_l hℳ Y.real (zero_l ℳ)
  · rintro ⟨α, Y, hαβ, hY, hXY⟩
    have hαM := (SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ α) hβM).mp hαβ
    obtain ⟨i, hi, him, hαi⟩ := SecondOrderRootCorrespondence.predecessor_exists_l hℳ A hP
      (SecondOrderOrdinalHistoryCoherence.ordinal_transitive_l hℳ A hA) α hm hαM
    obtain ⟨V, hV⟩ := SecondOrderSections.exists_l hℳ S i
    let L : SecondOrderGraph.code_l ℳ := ⟨V, zero_l ℳ, hS.wellFounded i V hV⟩
    have hL : SecondOrderRelativeLevel.spec_l hℳ B hB α L :=
      ⟨A, hA, Q, D, R, S, i, V, hP, hS, hi, hαi, hV, SecondOrderBisimulation.refl_l hℳ V (zero_l ℳ)⟩
    have hYL := SecondOrderRelativeLevel.unique_l hℳ (SecondOrderGraph.refl_l hℳ ⟨B, zero_l ℳ, hB⟩)
      (SecondOrderGraph.refl_l hℳ α) hY hL
    exact ⟨i, L, him, hV, rfl,
      (SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ X) hYL).mp hXY⟩

#print axioms value_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeLevelLimit
