import BMSConstructibleBridge.SecondOrderOrdinalSuccessor
import BMSConstructibleBridge.SecondOrderOrdinalStrongHierarchy

/-! # 相对层值的实际历史定义与唯一性

阶段由某个母序数中的规范成员表示，允许任意更大的母序数与不同编码。
所有存在性保留在 Prop；本文件只给出语义辅助，实际对象正文另行构造。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeLevel

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def spec_l (hℳ : Theory.Models ℳ theory_m) (B : set_l ℳ)
    (hB : SecondOrderDomain.wf_l B (zero_l ℳ)) (α C : SecondOrderGraph.code_l ℳ) : Prop :=
  ∃ A : SecondOrderGraph.code_l ℳ,
    SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ))
      (SecondOrderQuotient.mk_l hℳ A) ∧
    ∃ Q D R S : set_l ℳ, ∃ n : num_l ℳ, ∃ W : set_l ℳ,
      SecondOrderOrdinalHierarchy.presentation_l A Q D R ∧
      SecondOrderRelativeHierarchyStrongTheorem.spec_l B R S hB ∧ mem_l n D ∧
      SecondOrderBisimulation.eq_l α.real A.real α.root n ∧ SecondOrderSections.spec_l S n W ∧
      SecondOrderBisimulation.eq_l C.real W C.root (zero_l ℳ)

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (B : set_l ℳ)
    (hB : SecondOrderDomain.wf_l B (zero_l ℳ))
    (hBase : SecondOrderTransitiveSuperset.transitive_l ⟨B, zero_l ℳ, hB⟩)
    (α : SecondOrderGraph.code_l ℳ)
    (hα : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ))
      (SecondOrderQuotient.mk_l hℳ α)) : ∃ C, spec_l hℳ B hB α C := by
  obtain ⟨A, hA, hMem, _⟩ := SecondOrderOrdinalSuccessor.exists_l hℳ α hα
  obtain ⟨b, hb, hαb⟩ := hMem
  obtain ⟨Q, D, R, S, hP, hS⟩ := SecondOrderOrdinalStrongHierarchy.exists_l hℳ A hA B hB hBase
  obtain ⟨n, hn, hnb⟩ := SecondOrderRootRepresentatives.covers_l hℳ hP.equality hP.representatives hb
  have hαn := SecondOrderBisimulation.trans_l hℳ α.real A.real A.real α.root b n hαb
    (SecondOrderBisimulation.symm_l hℳ A.real A.real n b hnb)
  obtain ⟨W, hW⟩ := SecondOrderSections.exists_l hℳ S n
  exact ⟨⟨W, zero_l ℳ, hS.wellFounded n W hW⟩, A, hA, Q, D, R, S, n, W,
    hP, hS, hn, hαn, hW, SecondOrderBisimulation.refl_l hℳ W (zero_l ℳ)⟩

theorem unique_l (hℳ : Theory.Models ℳ theory_m) {B B' : set_l ℳ}
    {hB : SecondOrderDomain.wf_l B (zero_l ℳ)} {hB' : SecondOrderDomain.wf_l B' (zero_l ℳ)}
    (hBB' : SecondOrderGraph.eq_l ⟨B, zero_l ℳ, hB⟩ ⟨B', zero_l ℳ, hB'⟩)
    {α α' C C' : SecondOrderGraph.code_l ℳ} (hαα' : SecondOrderGraph.eq_l α α')
    (hC : spec_l hℳ B hB α C) (hC' : spec_l hℳ B' hB' α' C') : SecondOrderGraph.eq_l C C' := by
  obtain ⟨A, hA, Q, D, R, S, n, W, hP, hS, hn, hαn, hWn, hCW⟩ := hC
  obtain ⟨A', hA', Q', D', R', T, m, W', hP', hT, hm, hα'm, hW'm, hC'W'⟩ := hC'
  have hnm := SecondOrderBisimulation.trans_l hℳ A.real α.real A'.real n α.root m
    (SecondOrderBisimulation.symm_l hℳ α.real A.real α.root n hαn)
    (SecondOrderBisimulation.trans_l hℳ α.real α'.real A'.real α.root α'.root m hαα' hα'm)
  have hWW' := SecondOrderOrdinalHistoryCoherence.rows_l hℳ A A' hA hA' hBB' hP hP' hS hT
    hn hm hnm hWn hW'm
  exact SecondOrderGraph.trans_l hℳ
    (show SecondOrderGraph.eq_l C ⟨W, zero_l ℳ, hS.wellFounded n W hWn⟩ from hCW)
    (SecondOrderGraph.trans_l hℳ hWW'
      (SecondOrderGraph.symm_l hℳ
        (show SecondOrderGraph.eq_l C' ⟨W', zero_l ℳ, hT.wellFounded m W' hW'm⟩ from hC'W')))

theorem transfer_l (hℳ : Theory.Models ℳ theory_m) {B : set_l ℳ}
    {hB : SecondOrderDomain.wf_l B (zero_l ℳ)} {α α' C C' : SecondOrderGraph.code_l ℳ}
    (hαα' : SecondOrderGraph.eq_l α α') (hCC' : SecondOrderGraph.eq_l C C')
    (hC : spec_l hℳ B hB α C) : spec_l hℳ B hB α' C' := by
  obtain ⟨A, hA, Q, D, R, S, n, W, hP, hS, hn, hαn, hWn, hCW⟩ := hC
  exact ⟨A, hA, Q, D, R, S, n, W, hP, hS, hn,
    SecondOrderBisimulation.trans_l hℳ α'.real α.real A.real α'.root α.root n
      (SecondOrderBisimulation.symm_l hℳ α.real α'.real α.root α'.root hαα') hαn,
    hWn, SecondOrderBisimulation.trans_l hℳ C'.real C.real W C'.root C.root (zero_l ℳ)
      (SecondOrderBisimulation.symm_l hℳ C.real C'.real C.root C'.root hCC') hCW⟩

theorem congr_l (hℳ : Theory.Models ℳ theory_m) {B : set_l ℳ}
    {hB : SecondOrderDomain.wf_l B (zero_l ℳ)} {α α' C C' : SecondOrderGraph.code_l ℳ}
    (hαα' : SecondOrderGraph.eq_l α α') (hCC' : SecondOrderGraph.eq_l C C') :
    spec_l hℳ B hB α C ↔ spec_l hℳ B hB α' C' :=
  ⟨transfer_l hℳ hαα' hCC', transfer_l hℳ (SecondOrderGraph.symm_l hℳ hαα')
    (SecondOrderGraph.symm_l hℳ hCC')⟩

theorem exists_zero_l (hℳ : Theory.Models ℳ theory_m) (B : set_l ℳ)
    (hB : SecondOrderDomain.wf_l B (zero_l ℳ))
    (hBase : SecondOrderTransitiveSuperset.transitive_l ⟨B, zero_l ℳ, hB⟩)
    (α : SecondOrderGraph.code_l ℳ)
    (hα : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ))
      (SecondOrderQuotient.mk_l hℳ α)) :
    ∃ W : set_l ℳ, ∃ hW : SecondOrderDomain.wf_l W (zero_l ℳ), spec_l hℳ B hB α ⟨W, zero_l ℳ, hW⟩ := by
  obtain ⟨C, hC⟩ := exists_l hℳ B hB hBase α hα
  obtain ⟨W, hW, hWC⟩ := SecondOrderRootNormalization.normal_exists_l hℳ C
  exact ⟨W, hW, transfer_l hℳ (SecondOrderGraph.refl_l hℳ α) (SecondOrderGraph.symm_l hℳ hWC) hC⟩

#print axioms exists_l
#print axioms unique_l
#print axioms exists_zero_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeLevel
