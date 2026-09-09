import BMSConstructibleBridge.StageOrdinalDelta
import ConstructibleUniverse.SetTheory.ZFC.Constructible.FiniteOrdinalSuccessorFormula

/-!
# 后继极限序数的有界公式

本文件给出稳定关系两端所需的纯成员语言 `Delta0` 谓词。对一个 von Neumann
序数 `alpha`，它断言 `alpha` 非空，并且每个 `gamma ∈ alpha` 的 von Neumann
后继仍属于 `alpha`。这恰好等价于 `Order.IsSuccLimit alpha.rank`。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible

/-- `index` 坐标是非零且对 von Neumann 后继封闭的序数。 -/
def stageIsSuccLimitDeltaAt_l {arity : Nat} (index : Fin arity) :
    Delta0Formula arity :=
  .conj
    (finiteReflectionIsOrdinalDelta_l.rename ![index])
    (.conj
      (.boundedEx index (.eq (Fin.last arity) (Fin.last arity)))
      (.boundedAll index
        (.boundedEx index.castSucc
          (Delta0Formula.successorAt
            (Fin.last (arity + 1)) (Fin.last arity).castSucc))))

/-- 有界公式的外部语义：序数非空并且对后继封闭。 -/
theorem satisfies_stageIsSuccLimitDeltaAt_iff_l
    {arity : Nat} (index : Fin arity) (assignment : Tuple ZFSet.{u} arity)
    (hOrdinal : (assignment index).IsOrdinal) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        (stageIsSuccLimitDeltaAt_l index) assignment ↔
      (∃ member, member ∈ assignment index) ∧
        ∀ member, member ∈ assignment index →
          insert member member ∈ assignment index := by
  simp only [stageIsSuccLimitDeltaAt_l, Delta0Formula.Satisfies,
    Delta0Formula.satisfies_rename, Delta0Formula.satisfies_boundedAll,
    Delta0Formula.satisfies_successorAt, snoc_last, snoc_castSucc]
  have hRenamed :
      (fun position : Fin 1 => assignment (![index] position)) =
        ![assignment index] := by
    funext position
    fin_cases position
    rfl
  rw [hRenamed]
  have hOrdinalSemantic :
      Delta0Formula.Satisfies Delta0Formula.ZFMem
          finiteReflectionIsOrdinalDelta_l ![assignment index] ↔
        (assignment index).IsOrdinal := by
    rw [ZFSet.isOrdinal_iff_forall_mem_isTransitive]
    simp only [finiteReflectionIsOrdinalDelta_l,
      Delta0Formula.Satisfies, Delta0Formula.satisfies_boundedAll,
      snoc_last, snoc_castSucc]
    rfl
  rw [hOrdinalSemantic]
  simp only [hOrdinal, true_and]
  constructor
  · rintro ⟨⟨member, hMember, _⟩, hClosed⟩
    refine ⟨⟨member, hMember⟩, ?_⟩
    intro member hMember
    rcases hClosed member hMember with ⟨successor, hSuccessor, hEqual⟩
    simpa only [hEqual] using hSuccessor
  · rintro ⟨⟨member, hMember⟩, hClosed⟩
    refine ⟨⟨member, hMember, trivial⟩, ?_⟩
    intro member hMember
    exact ⟨insert member member, hClosed member hMember, rfl⟩

/-- 在已知坐标为序数时，有界谓词精确表达其 rank 是后继极限。 -/
theorem satisfies_stageIsSuccLimitDeltaAt_iff_rank_l
    {arity : Nat} (index : Fin arity) (assignment : Tuple ZFSet.{u} arity)
    (hOrdinal : (assignment index).IsOrdinal) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        (stageIsSuccLimitDeltaAt_l index) assignment ↔
      Order.IsSuccLimit (assignment index).rank := by
  rw [satisfies_stageIsSuccLimitDeltaAt_iff_l index assignment hOrdinal]
  rw [Ordinal.isSuccLimit_iff]
  constructor
  · rintro ⟨hNonempty, hClosed⟩
    refine ⟨?_, Order.isSuccPrelimit_of_succ_lt ?_⟩
    · intro hZero
      rcases hNonempty with ⟨member, hMember⟩
      have hValue : assignment index = (assignment index).rank.toZFSet :=
        hOrdinal.toZFSet_rank_eq.symm
      rw [hValue, hZero] at hMember
      simpa using hMember
    · intro ordinal hOrdinalRank
      have hMember : ordinal.toZFSet ∈ assignment index := by
        rw [← hOrdinal.toZFSet_rank_eq]
        exact Ordinal.toZFSet_mem_toZFSet_iff.mpr hOrdinalRank
      have hSuccessor := hClosed ordinal.toZFSet hMember
      have hSuccessorCode :
          insert ordinal.toZFSet ordinal.toZFSet =
            (Order.succ ordinal).toZFSet := by
        simpa only [Order.succ_eq_add_one] using
          (Ordinal.toZFSet_add_one ordinal).symm
      rw [hSuccessorCode, ← hOrdinal.toZFSet_rank_eq] at hSuccessor
      exact Ordinal.toZFSet_mem_toZFSet_iff.mp hSuccessor
  · rintro ⟨hNonzero, hPrelimit⟩
    refine ⟨?_, ?_⟩
    · refine ⟨(0 : Ordinal).toZFSet, ?_⟩
      rw [← hOrdinal.toZFSet_rank_eq]
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr
        (pos_iff_ne_zero.mpr hNonzero)
    · intro member hMember
      have hMemberOrdinal : member.IsOrdinal := hOrdinal.mem hMember
      have hRankLt : member.rank < (assignment index).rank := by
        apply Ordinal.toZFSet_mem_toZFSet_iff.mp
        simpa only [hMemberOrdinal.toZFSet_rank_eq,
          hOrdinal.toZFSet_rank_eq] using hMember
      have hSuccLt : Order.succ member.rank < (assignment index).rank :=
        (Order.isSuccPrelimit_iff_succ_lt.mp hPrelimit) member.rank hRankLt
      have hSuccessorCode : insert member member =
          (Order.succ member.rank).toZFSet := by
        calc
          insert member member =
              insert member.rank.toZFSet member.rank.toZFSet := by
                rw [hMemberOrdinal.toZFSet_rank_eq]
          _ = (member.rank + 1).toZFSet :=
            (Ordinal.toZFSet_add_one member.rank).symm
          _ = (Order.succ member.rank).toZFSet := by
            rw [Order.succ_eq_add_one]
      rw [hSuccessorCode, ← hOrdinal.toZFSet_rank_eq]
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr hSuccLt

/-- 在任意可构造层中，后继极限公式保持上述 rank 语义。 -/
theorem satisfiesIn_stageIsSuccLimitDeltaAt_iff_rank_l
    {top : Ordinal.{u}} {arity : Nat} (index : Fin arity)
    (assignment : Tuple (StageCarrier top) arity)
    (hOrdinal : (assignment index).1.IsOrdinal) :
    FOFormula.Satisfies
        (fun first second : StageCarrier top => first.1 ∈ second.1)
        (stageIsSuccLimitDeltaAt_l index).toFO assignment ↔
      Order.IsSuccLimit (assignment index).1.rank := by
  rw [Delta0Formula.satisfies_toFO]
  change Delta0Formula.Satisfies (zfCarrierMem (LStageZF top))
      (stageIsSuccLimitDeltaAt_l index) assignment ↔ _
  have hAbsolute := Delta0Formula.satisfies_absolute
    (LStageZF_isTransitive top) (stageIsSuccLimitDeltaAt_l index) assignment
  rw [hAbsolute]
  exact satisfies_stageIsSuccLimitDeltaAt_iff_rank_l index
    (Delta0Formula.val assignment) hOrdinal

/-- 原始集合赋值版本，便于把该谓词嵌入更大的层内公式。 -/
theorem satisfiesIn_stageIsSuccLimitDeltaAt_iff_rank_raw_l
    {top : Ordinal.{u}} {arity : Nat} (index : Fin arity)
    (assignment : Tuple ZFSet.{u} arity)
    (hAssignment : ∀ position, assignment position ∈ LStageZF top)
    (hOrdinal : (assignment index).IsOrdinal) :
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        (stageIsSuccLimitDeltaAt_l index).toFO assignment ↔
      Order.IsSuccLimit (assignment index).rank := by
  let stageAssignment : Tuple (StageCarrier top) arity :=
    fun position => ⟨assignment position, hAssignment position⟩
  have hBridge := Model.satisfies_stageCarrier_iff_satisfiesIn
    (stageIsSuccLimitDeltaAt_l index).toFO stageAssignment
  have hValue : (fun position => (stageAssignment position).1) = assignment := by
    rfl
  rw [hValue] at hBridge
  exact hBridge.symm.trans
    (satisfiesIn_stageIsSuccLimitDeltaAt_iff_rank_l
      index stageAssignment hOrdinal)

end YesMetaZFC.BMS.ConstructibleBridge
