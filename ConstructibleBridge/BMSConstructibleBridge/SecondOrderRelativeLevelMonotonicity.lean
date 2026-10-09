import BMSConstructibleBridge.SecondOrderRelativeLevelProperties

/-! # 不同母历史中的相对层值严格增长

把较小序数定位到较大阶段所在母序数的规范前驱，然后用已证明的层值唯一性
换码。由此跨任意呈现得到强隶属及子集单调，不要求调用者预先共用历史。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeLevelMonotonicity

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem members_l (hℳ : Theory.Models ℳ theory_m) {B B' : set_l ℳ}
    {hB : SecondOrderDomain.wf_l B (zero_l ℳ)} {hB' : SecondOrderDomain.wf_l B' (zero_l ℳ)}
    (hBB' : SecondOrderGraph.eq_l ⟨B, zero_l ℳ, hB⟩ ⟨B', zero_l ℳ, hB'⟩)
    {α β C C' : SecondOrderGraph.code_l ℳ} (hαβ : SecondOrderGraph.mem_l α β)
    (hC : SecondOrderRelativeLevel.spec_l hℳ B hB α C)
    (hC' : SecondOrderRelativeLevel.spec_l hℳ B' hB' β C') : SecondOrderGraph.mem_l C C' := by
  obtain ⟨A, hA, Q, D, R, T, m, W, hP, hT, hm, hβm, hWm, hC'W⟩ := hC'
  have hβM : SecondOrderGraph.eq_l β (SecondOrderRootCorrespondence.member_code_l hℳ A hP m hm) := hβm
  have hαM := (SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ α) hβM).mp hαβ
  obtain ⟨n, hn, hnm, hαn⟩ := SecondOrderRootCorrespondence.predecessor_exists_l hℳ A hP
    (SecondOrderOrdinalHistoryCoherence.ordinal_transitive_l hℳ A hA) α hm hαM
  obtain ⟨V, hVn⟩ := SecondOrderSections.exists_l hℳ T n
  let L : SecondOrderGraph.code_l ℳ := ⟨V, zero_l ℳ, hT.wellFounded n V hVn⟩
  have hL : SecondOrderRelativeLevel.spec_l hℳ B' hB' α L :=
    ⟨A, hA, Q, D, R, T, n, V, hP, hT, hn, hαn, hVn,
      SecondOrderBisimulation.refl_l hℳ V (zero_l ℳ)⟩
  have hCL := SecondOrderRelativeLevel.unique_l hℳ hBB' (SecondOrderGraph.refl_l hℳ α) hC hL
  have hLW := hT.members m n hnm V W L.wf (hT.wellFounded m W hWm) hVn hWm
  exact (SecondOrderGraph.mem_congr_l hℳ hCL
    (show SecondOrderGraph.eq_l C' ⟨W, zero_l ℳ, hT.wellFounded m W hWm⟩ from hC'W)).mpr hLW

theorem subset_l (hℳ : Theory.Models ℳ theory_m) {B B' : set_l ℳ}
    {hB : SecondOrderDomain.wf_l B (zero_l ℳ)} {hB' : SecondOrderDomain.wf_l B' (zero_l ℳ)}
    (hBB' : SecondOrderGraph.eq_l ⟨B, zero_l ℳ, hB⟩ ⟨B', zero_l ℳ, hB'⟩)
    {α β C C' : SecondOrderGraph.code_l ℳ} (hαβ : SecondOrderGraph.mem_l α β)
    (hC : SecondOrderRelativeLevel.spec_l hℳ B hB α C)
    (hC' : SecondOrderRelativeLevel.spec_l hℳ B' hB' β C') : SecondOrderGraphSubsetFormula.subset_l C C' := by
  intro X hX
  exact SecondOrderRelativeLevelProperties.transitive_l hℳ hC' C X
    (members_l hℳ hBB' hαβ hC hC') hX

#print axioms members_l
#print axioms subset_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeLevelMonotonicity
