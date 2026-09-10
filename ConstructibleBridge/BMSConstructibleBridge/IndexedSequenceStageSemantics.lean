import BMSConstructibleBridge.TextbookNaturalArithmeticStage

/-!
# 有限索引序列的共同层内语义

函数图读取、取值唯一性及全域性只依赖传递载体，与所编码的分类记录无关。
三种痕迹分类器共用此处证明；原有公开定理名保持不变。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

theorem satisfiesIn_functionGraphValueAt_iff_l
    {M : ZFSet.{u}} (hM : M.IsTransitive) {n : Nat}
    (graph value index : Fin n) (assignment : Tuple ZFSet.{u} n)
    (hAssignment : ∀ position, assignment position ∈ M) :
    Model.SatisfiesIn (M : Set ZFSet.{u})
        (IndexedSequenceZF.functionGraphValueAt graph value index)
        assignment ↔
      ZFSet.pair (assignment value) (assignment index) ∈ assignment graph := by
  rw [IndexedSequenceZF.functionGraphValueAt,
    Model.satisfiesIn_delta0_iff hM _ assignment hAssignment]
  simpa only [IndexedSequenceZF.functionGraphValueAt] using
    (IndexedSequenceZF.satisfies_functionGraphValueAt
      graph value index assignment)

theorem satisfiesIn_all_trace_iff
    (M : Set ZFSet.{u}) {n : Nat} (formula : FOFormula (n + 1))
    (assignment : Tuple ZFSet.{u} n) :
    Model.SatisfiesIn M (FOFormula.all formula) assignment ↔
      ∀ value : ZFSet.{u}, value ∈ M →
        Model.SatisfiesIn M formula (snoc assignment value) := by
  classical
  simp [FOFormula.all, Model.SatisfiesIn]

theorem satisfiesIn_imp_trace_iff
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (assignment : Tuple ZFSet.{u} n) :
    Model.SatisfiesIn M (FOFormula.imp left right) assignment ↔
      (Model.SatisfiesIn M left assignment →
        Model.SatisfiesIn M right assignment) := by
  classical
  simp only [FOFormula.imp, FOFormula.disj, Model.SatisfiesIn]
  tauto

theorem satisfiesIn_uniqueValueAtBody_iff_l
    {M : ZFSet.{u}} (hM : M.IsTransitive)
    (omega sequence length graph index value : ZFSet.{u})
    (hOmega : omega ∈ M) (hSequence : sequence ∈ M)
    (hLength : length ∈ M) (hGraph : graph ∈ M)
    (hIndex : index ∈ M) (hValue : value ∈ M) :
    Model.SatisfiesIn (M : Set ZFSet.{u})
        IndexedSequenceZF.uniqueValueAtBody
        ![omega, sequence, length, graph, index, value] ↔
      ZFSet.pair value index ∈ graph ∧
        ∀ other : ZFSet.{u}, other ∈ M →
          ZFSet.pair other index ∈ graph → other = value := by
  rw [IndexedSequenceZF.uniqueValueAtBody]
  simp only [Model.SatisfiesIn, satisfiesIn_all_trace_iff,
    Model.snoc_eq_finSnoc]
  rw [satisfiesIn_functionGraphValueAt_iff_l hM
    (3 : Fin 6) (5 : Fin 6) (4 : Fin 6) _ (by
      intro position
      fin_cases position <;> assumption)]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro other
  apply imp_congr_right
  intro hOther
  rw [show IndexedSequenceZF.formulaImp
      (IndexedSequenceZF.functionGraphValueAt
        (3 : Fin 7) (6 : Fin 7) (4 : Fin 7))
      (.eq (6 : Fin 7) (5 : Fin 7)) =
      FOFormula.imp
        (IndexedSequenceZF.functionGraphValueAt
          (3 : Fin 7) (6 : Fin 7) (4 : Fin 7))
        (.eq (6 : Fin 7) (5 : Fin 7)) by rfl,
    satisfiesIn_imp_trace_iff,
    satisfiesIn_functionGraphValueAt_iff_l hM
    (3 : Fin 7) (6 : Fin 7) (4 : Fin 7) _ (by
      intro position
      fin_cases position <;> assumption)]
  rfl

theorem satisfiesIn_totalFunctionalBody_iff_l
    {M : ZFSet.{u}} (hM : M.IsTransitive)
    (omega sequence length graph index : ZFSet.{u})
    (hOmega : omega ∈ M) (hSequence : sequence ∈ M)
    (hLength : length ∈ M) (hGraph : graph ∈ M)
    (hIndex : index ∈ M) :
    Model.SatisfiesIn (M : Set ZFSet.{u})
        IndexedSequenceZF.totalFunctionalBody
        ![omega, sequence, length, graph, index] ↔
      (index ∈ length →
        ∃ value : ZFSet.{u}, value ∈ M ∧
          ZFSet.pair value index ∈ graph ∧
          ∀ other : ZFSet.{u}, other ∈ M →
            ZFSet.pair other index ∈ graph → other = value) := by
  rw [IndexedSequenceZF.totalFunctionalBody]
  rw [show IndexedSequenceZF.formulaImp
      (.mem (4 : Fin 5) (2 : Fin 5))
      (.ex IndexedSequenceZF.uniqueValueAtBody) =
      FOFormula.imp (.mem (4 : Fin 5) (2 : Fin 5))
        (.ex IndexedSequenceZF.uniqueValueAtBody) by rfl,
    satisfiesIn_imp_trace_iff]
  apply imp_congr_right
  intro _hIndexLength
  change (∃ value : ZFSet.{u}, value ∈ M ∧
    Model.SatisfiesIn (M : Set ZFSet.{u})
      IndexedSequenceZF.uniqueValueAtBody
      ![omega, sequence, length, graph, index, value]) ↔ _
  apply exists_congr
  intro value
  constructor
  · rintro ⟨hValue, hUnique⟩
    exact ⟨hValue,
      (satisfiesIn_uniqueValueAtBody_iff_l hM
        omega sequence length graph index value hOmega hSequence hLength
          hGraph hIndex hValue).mp hUnique⟩
  · rintro ⟨hValue, hUnique⟩
    exact ⟨hValue,
      (satisfiesIn_uniqueValueAtBody_iff_l hM
        omega sequence length graph index value hOmega hSequence hLength
          hGraph hIndex hValue).mpr hUnique⟩

theorem satisfiesIn_valueAtFormula_iff_l
    {M : ZFSet.{u}} (hM : M.IsTransitive)
    (assignment : Tuple ZFSet.{u} 3)
    (hAssignment : ∀ position, assignment position ∈ M) :
    Model.SatisfiesIn (M : Set ZFSet.{u})
        IndexedSequenceZF.valueAtFormula assignment ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        IndexedSequenceZF.valueAtFormula assignment := by
  rw [IndexedSequenceZF.valueAtFormula]
  exact Model.satisfiesIn_delta0_iff hM
    IndexedSequenceZF.valueAtDelta0 assignment hAssignment

end YesMetaZFC.BMS.ConstructibleBridge
