import BMSConstructibleBridge.BoundedExternalStageElementarity
import ConstructibleUniverse.SetTheory.ZFC.Constructible.FormulaSyntaxCode
import ConstructibleUniverse.SetTheory.ZFC.Constructible.Reflection
import ConstructibleUniverse.SetTheory.ZFC.Constructible.BareStageHistoryBounds

/-!
# 可构造宇宙的全公式同时反射层

固定公式的反射定理不足以直接构造 Hunter 意义下同时对所有有限层稳定的
序数。本模块利用 `PackedFormula` 的自然数枚举，在每一步同时越过全部公式
所需的见证闭包界，再取一条严格递增的 omega 链之上确界。所得层对每个
有限元成员公式都与整个 `L` 绝对。

这里的公式枚举和见证选择都只发生在 Lean 元理论中；结论仍是外部 Tarski
满足关系的逐公式定理，不引入真谓词或额外公理。
-/

open Set

universe u

namespace YesMetaZFC
namespace BMS
namespace ConstructibleBridge

open Constructible
open Constructible.FOFormulaCode

/-- 一步中所有公式的闭包界之上确界。 -/
noncomputable def fullClosingBound_l (alpha : Ordinal.{u}) : Ordinal.{u} :=
  iSup fun code : Nat =>
    closingBound (packedFormulaNatEnumerate code).2 alpha

/-- 每个指定公式的闭包界都不超过同时闭包界。 -/
theorem closingBound_le_fullClosingBound_l
    {arity : Nat} (formula : FOFormula arity) (alpha : Ordinal.{u}) :
    closingBound formula alpha <= fullClosingBound_l alpha := by
  let packed : PackedFormula := ⟨arity, formula⟩
  have hBound := Ordinal.le_iSup
    (fun code : Nat =>
      closingBound (packedFormulaNatEnumerate code).2 alpha)
    (packedFormulaNatCode packed)
  change closingBound
      (packedFormulaNatEnumerate (packedFormulaNatCode packed)).2 alpha <=
    fullClosingBound_l alpha at hBound
  rw [packedFormulaNatEnumerate_packedFormulaNatCode] at hBound
  exact hBound

/-- 同时反射的一步严格越过全部公式的闭包界。 -/
noncomputable def fullReflectionStep_l
    (alpha : Ordinal.{u}) : Ordinal.{u} :=
  Order.succ (fullClosingBound_l alpha)

/-- 同时反射步严格增加序数。 -/
theorem lt_fullReflectionStep_l (alpha : Ordinal.{u}) :
    alpha < fullReflectionStep_l alpha := by
  have hAlpha : alpha <= fullClosingBound_l alpha :=
    (le_closingBound (defaultFormula 0) alpha).trans
      (closingBound_le_fullClosingBound_l (defaultFormula 0) alpha)
  exact hAlpha.trans_lt (Order.lt_succ _)

/-- 同时反射的一步对任意指定公式都提供见证闭包。 -/
theorem closesFrom_fullReflectionStep_l
    {arity : Nat} (formula : FOFormula arity) (alpha : Ordinal.{u}) :
    ClosesFrom formula alpha (fullReflectionStep_l alpha) := by
  exact (closesFrom_closingBound formula alpha).mono_right
    ((closingBound_le_fullClosingBound_l formula alpha).trans
      (Order.le_succ _))

/-- 从任意起点迭代全部公式的同时反射步。 -/
noncomputable def fullReflectionSequence_l
    (start : Ordinal.{u}) : Nat -> Ordinal.{u}
  | 0 => start
  | index + 1 => fullReflectionStep_l (fullReflectionSequence_l start index)

@[simp]
theorem fullReflectionSequence_zero_l (start : Ordinal.{u}) :
    fullReflectionSequence_l start 0 = start :=
  rfl

@[simp]
theorem fullReflectionSequence_succ_l
    (start : Ordinal.{u}) (index : Nat) :
    fullReflectionSequence_l start (index + 1) =
      fullReflectionStep_l (fullReflectionSequence_l start index) :=
  rfl

/-- 同时反射序列的相邻项严格递增。 -/
theorem fullReflectionSequence_lt_succ_l
    (start : Ordinal.{u}) (index : Nat) :
    fullReflectionSequence_l start index <
      fullReflectionSequence_l start (index + 1) := by
  rw [fullReflectionSequence_succ_l]
  exact lt_fullReflectionStep_l _

/-- 同时反射序列严格单调。 -/
theorem fullReflectionSequence_strictMono_l (start : Ordinal.{u}) :
    StrictMono (fullReflectionSequence_l start) :=
  strictMono_nat_of_lt_succ (fullReflectionSequence_lt_succ_l start)

/-- 同时反射序列的极限。 -/
noncomputable def fullReflectionOrdinal_l
    (start : Ordinal.{u}) : Ordinal.{u} :=
  iSup (fullReflectionSequence_l start)

/-- 序列的每一项都不超过其极限。 -/
theorem fullReflectionSequence_le_ordinal_l
    (start : Ordinal.{u}) (index : Nat) :
    fullReflectionSequence_l start index <= fullReflectionOrdinal_l start :=
  Ordinal.le_iSup (fullReflectionSequence_l start) index

/-- 序列的每一项都严格小于其极限。 -/
theorem fullReflectionSequence_lt_ordinal_l
    (start : Ordinal.{u}) (index : Nat) :
    fullReflectionSequence_l start index < fullReflectionOrdinal_l start :=
  (fullReflectionSequence_lt_succ_l start index).trans_le
    (fullReflectionSequence_le_ordinal_l start (index + 1))

/-- 同时反射极限是非零后继极限。 -/
theorem fullReflectionOrdinal_isSuccLimit_l (start : Ordinal.{u}) :
    Order.IsSuccLimit (fullReflectionOrdinal_l start) := by
  rw [Order.isSuccLimit_iff]
  constructor
  · exact not_isMin_iff.mpr
      ⟨fullReflectionSequence_l start 0,
        fullReflectionSequence_lt_ordinal_l start 0⟩
  · apply Order.isSuccPrelimit_of_succ_lt
    intro gamma hGamma
    apply Ordinal.succ_lt_iSup_of_ne_iSup
      (f := fullReflectionSequence_l start)
    · intro index hEqual
      exact (fullReflectionSequence_lt_ordinal_l start index).ne hEqual
    · exact hGamma

/-- 起点不超过同时反射极限。 -/
theorem le_fullReflectionOrdinal_l (start : Ordinal.{u}) :
    start <= fullReflectionOrdinal_l start := by
  simpa only [fullReflectionSequence_zero_l] using
    fullReflectionSequence_le_ordinal_l start 0

/-- 极限中的每个有限元组已经共同出现于某个序列项。 -/
theorem exists_fullReflectionSequence_for_tuple_l
    {arity : Nat} (start : Ordinal.{u})
    (assignment : Tuple ZFSet.{u} arity)
    (hAssignment : forall index,
      assignment index ∈ LStageZF (fullReflectionOrdinal_l start)) :
    exists stage : Nat, forall index,
      assignment index ∈ LStageZF (fullReflectionSequence_l start stage) := by
  induction arity with
  | zero =>
      exact ⟨0, fun index => Fin.elim0 index⟩
  | succ arity inductionHypothesis =>
      let initial : Tuple ZFSet.{u} arity :=
        fun index => assignment index.castSucc
      have hInitial : forall index,
          initial index ∈ LStageZF (fullReflectionOrdinal_l start) :=
        fun index => hAssignment index.castSucc
      rcases inductionHypothesis initial hInitial with ⟨leftStage, hLeft⟩
      have hLast := hAssignment (Fin.last arity)
      rcases (mem_LStageZF_limit_iff
        (fullReflectionOrdinal_isSuccLimit_l start)).mp hLast with
        ⟨gamma, hGamma, hLastGamma⟩
      rcases Ordinal.lt_iSup_iff.mp hGamma with ⟨rightStage, hGammaStage⟩
      refine ⟨max leftStage rightStage, ?_⟩
      intro index
      refine Fin.lastCases ?_ (fun prior => ?_) index
      · exact LStageZF_mono
          ((fullReflectionSequence_strictMono_l start).monotone
            (Nat.le_max_right leftStage rightStage))
          (LStageZF_mono hGammaStage.le hLastGamma)
      · exact LStageZF_mono
          ((fullReflectionSequence_strictMono_l start).monotone
            (Nat.le_max_left leftStage rightStage))
          (hLeft prior)

/-- 同时反射极限对每个外部成员公式都在自身处闭合。 -/
theorem closesFrom_fullReflectionOrdinal_l
    {arity : Nat} (formula : FOFormula arity) (start : Ordinal.{u}) :
    ClosesFrom formula (fullReflectionOrdinal_l start)
      (fullReflectionOrdinal_l start) := by
  apply closesFrom_of_cofinal_sequence formula
    (fullReflectionSequence_l start) (fullReflectionOrdinal_l start)
  · intro tupleArity assignment hAssignment
    exact exists_fullReflectionSequence_for_tuple_l start assignment hAssignment
  · intro index
    rw [fullReflectionSequence_succ_l]
    exact closesFrom_fullReflectionStep_l formula _
  · intro index
    exact fullReflectionSequence_le_ordinal_l start (index + 1)

/-- 同时反射极限与整个可构造宇宙对所有公式绝对。 -/
theorem fullReflectionOrdinal_satisfactionAbsolute_l
    (start : Ordinal.{u}) :
    SatisfactionAbsolute
      (LStageZF (fullReflectionOrdinal_l start) : Set ZFSet.{u}) L := by
  intro arity formula assignment hAssignment
  exact satisfiesIn_stage_iff_L_of_closes formula
    (fullReflectionOrdinal_l start)
    (closesFrom_fullReflectionOrdinal_l formula start)
    assignment hAssignment

/-- 同时反射极限层非空；空集已经出现在每个后继极限层中。 -/
theorem fullReflectionOrdinal_nonempty_l (start : Ordinal.{u}) :
    Nonempty (StageCarrier (fullReflectionOrdinal_l start)) :=
  ⟨⟨∅, empty_mem_LStageZF_of_isSuccLimit
    (fullReflectionOrdinal_isSuccLimit_l start)⟩⟩

/-- 在一个全反射层之上再取全反射层。 -/
noncomputable def nextFullReflectionOrdinal_l
    (alpha : Ordinal.{u}) : Ordinal.{u} :=
  fullReflectionOrdinal_l (Order.succ alpha)

/-- 下一个全反射层严格位于给定层之上。 -/
theorem lt_nextFullReflectionOrdinal_l (alpha : Ordinal.{u}) :
    alpha < nextFullReflectionOrdinal_l alpha :=
  (Order.lt_succ alpha).trans_le
    (le_fullReflectionOrdinal_l (Order.succ alpha))

/--
两个相继构造的全反射层对每个有限 `Sigma` 公式初等。证明把两层的
满足关系分别与整个 `L` 比较，不需要重新进行公式归纳。
-/
theorem externalStageSigmaElementaryAt_fullReflection_l
    (level : Nat) (start : Ordinal.{u}) :
    ExternalStageSigmaElementaryAt_l level
      (fullReflectionOrdinal_l start)
      (nextFullReflectionOrdinal_l (fullReflectionOrdinal_l start)) := by
  let alpha := fullReflectionOrdinal_l start
  let beta := nextFullReflectionOrdinal_l alpha
  have hAlphaBeta : alpha <= beta :=
    (lt_nextFullReflectionOrdinal_l alpha).le
  refine ⟨fullReflectionOrdinal_nonempty_l start,
    fullReflectionOrdinal_nonempty_l (Order.succ alpha),
    hAlphaBeta, ?_⟩
  intro arity formula _hFormula assignment
  rw [Model.satisfies_stageCarrier_iff_satisfiesIn,
    Model.satisfies_stageCarrier_iff_satisfiesIn]
  change Model.SatisfiesIn
      (LStageZF (fullReflectionOrdinal_l start) : Set ZFSet.{u}) formula
      (fun index => (assignment index).1) <->
    Model.SatisfiesIn
      (LStageZF
        (fullReflectionOrdinal_l
          (Order.succ (fullReflectionOrdinal_l start))) : Set ZFSet.{u}) formula
      (fun index => (assignment index).1)
  rw [fullReflectionOrdinal_satisfactionAbsolute_l start formula
      (fun index => (assignment index).1) (fun index => (assignment index).2),
    fullReflectionOrdinal_satisfactionAbsolute_l (Order.succ alpha) formula
      (fun index => (assignment index).1)]
  intro index
  exact LStageZF_mono hAlphaBeta (assignment index).2

/--
同一对全反射层也对保留真正有界量词的有限 Levy 分类初等。这里实际上证明了
任意外部有限元公式的绝对性，所以分类证书只用于确定公开接口的数学含义。
-/
theorem boundedExternalStageSigmaElementaryAt_fullReflection_l
    (level : Nat) (start : Ordinal.{u}) :
    BoundedExternalStageSigmaElementaryAt_l level
      (fullReflectionOrdinal_l start)
      (nextFullReflectionOrdinal_l (fullReflectionOrdinal_l start)) := by
  let alpha := fullReflectionOrdinal_l start
  let beta := nextFullReflectionOrdinal_l alpha
  have hAlphaBeta : alpha ≤ beta :=
    (lt_nextFullReflectionOrdinal_l alpha).le
  refine ⟨fullReflectionOrdinal_nonempty_l start,
    fullReflectionOrdinal_nonempty_l (Order.succ alpha),
    hAlphaBeta, ?_⟩
  intro arity formula _hFormula assignment
  rw [Model.satisfies_stageCarrier_iff_satisfiesIn,
    Model.satisfies_stageCarrier_iff_satisfiesIn]
  change Model.SatisfiesIn
      (LStageZF (fullReflectionOrdinal_l start) : Set ZFSet.{u}) formula
      (fun index => (assignment index).1) ↔
    Model.SatisfiesIn
      (LStageZF
        (fullReflectionOrdinal_l
          (Order.succ (fullReflectionOrdinal_l start))) : Set ZFSet.{u}) formula
      (fun index => (assignment index).1)
  rw [fullReflectionOrdinal_satisfactionAbsolute_l start formula
      (fun index => (assignment index).1) (fun index => (assignment index).2),
    fullReflectionOrdinal_satisfactionAbsolute_l (Order.succ alpha) formula
      (fun index => (assignment index).1)]
  intro index
  exact LStageZF_mono hAlphaBeta (assignment index).2

end ConstructibleBridge
end BMS
end YesMetaZFC
