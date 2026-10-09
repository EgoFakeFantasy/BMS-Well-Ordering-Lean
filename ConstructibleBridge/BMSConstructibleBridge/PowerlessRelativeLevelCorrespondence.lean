import BMSConstructibleBridge.PowerlessRelativeHierarchyAgreement
import BMSConstructibleBridge.PowerlessRelativeHierarchyRealization

/-! # 纯集合层值与实际原图历史的双向对应

纯层值可由任意集合函数历史见证。反向用对象可定义归纳得到的历史唯一性，
不只检查规范扩张；全程保留传递基集条件，不暗加完整源理论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLevelCorrespondence

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderQuotient (type_l mk_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem forward_l (hℳ : Theory.Models ℳ theory_m) {B : set_l ℳ}
    {hB : SecondOrderDomain.wf_l B (zero_l ℳ)}
    (hBase : SecondOrderTransitiveSuperset.transitive_l ⟨B, zero_l ℳ, hB⟩)
    {α C : SecondOrderGraph.code_l ℳ} (hC : SecondOrderRelativeLevel.spec_l hℳ B hB α C) :
    PowerlessRelativeHierarchySemantics.level_l hℳ (mk_l hℳ ⟨B, zero_l ℳ, hB⟩) (mk_l hℳ α) (mk_l hℳ C) := by
  have hOriginal := hC
  obtain ⟨A, hA, Q, D, R, S, n, W, hP, _, hn, hαn, _, _⟩ := hC
  have hαN : SecondOrderGraph.eq_l α (SecondOrderRootCorrespondence.member_code_l hℳ A hP n hn) := hαn
  have hαA : SecondOrderGraph.mem_l α A :=
    (SecondOrderGraph.mem_congr_l hℳ hαN (SecondOrderGraph.refl_l hℳ A)).mpr
      (SecondOrderGraph.child_mem_l hℳ A n ((hP.representatives n).mp hn).1)
  obtain ⟨T, f, _, hMap, hf⟩ := SecondOrderRelativeLevelMap.exists_l hℳ B hB hBase A hA
  obtain ⟨d, ⟨_, hd⟩, _⟩ := hMap.2 (mk_l hℳ α) hαA
  have hLevelD := ((SecondOrderRelativeLevelRelation.value_iff_l hℳ hf _ _).mp hd).2.2
  have hCd := SecondOrderRelativeLevelRelation.quotient_unique_l hℳ
    ((SecondOrderRelativeLevelRelation.quotient_code_l hℳ α C).mpr hOriginal) hLevelD
  rw [← hCd] at hd
  exact ⟨mk_l hℳ A, f, mk_l hℳ T, hA, hαA,
    PowerlessRelativeHierarchyRealization.history_l hℳ hA hMap hf, hd⟩

theorem reverse_l (hℳ : Theory.Models ℳ theory_m) {B : set_l ℳ}
    {hB : SecondOrderDomain.wf_l B (zero_l ℳ)}
    (hBase : SecondOrderTransitiveSuperset.transitive_l ⟨B, zero_l ℳ, hB⟩)
    {α C : SecondOrderGraph.code_l ℳ}
    (hC : PowerlessRelativeHierarchySemantics.level_l hℳ
      (mk_l hℳ ⟨B, zero_l ℳ, hB⟩) (mk_l hℳ α) (mk_l hℳ C)) :
    SecondOrderRelativeLevel.spec_l hℳ B hB α C := by
  have hOriginal := hC
  obtain ⟨A, _, _, hA, hαA, _, _⟩ := hC
  have hα : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ))
      (mk_l hℳ α) := by
    apply SetTheory.Structure.IsOrdinal.mem hA
    exact hαA
  obtain ⟨D, hD⟩ := SecondOrderRelativeLevel.exists_l hℳ B hB hBase α hα
  have hCD := PowerlessRelativeHierarchyAgreement.level_unique_l hℳ hOriginal (forward_l hℳ hBase hD)
  exact SecondOrderRelativeLevel.transfer_l hℳ (SecondOrderGraph.refl_l hℳ α)
    ((SecondOrderQuotient.eq_iff_l hℳ D C).mp hCD.symm) hD

theorem iff_l (hℳ : Theory.Models ℳ theory_m) {B : set_l ℳ}
    {hB : SecondOrderDomain.wf_l B (zero_l ℳ)}
    (hBase : SecondOrderTransitiveSuperset.transitive_l ⟨B, zero_l ℳ, hB⟩)
    (α C : SecondOrderGraph.code_l ℳ) :
    PowerlessRelativeHierarchySemantics.level_l hℳ (mk_l hℳ ⟨B, zero_l ℳ, hB⟩) (mk_l hℳ α) (mk_l hℳ C) ↔
      SecondOrderRelativeLevel.spec_l hℳ B hB α C := ⟨reverse_l hℳ hBase, forward_l hℳ hBase⟩

#print axioms iff_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLevelCorrespondence
