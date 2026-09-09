import BMSConstructibleBridge.TextbookBoundedLevyCode
import BMSConstructibleBridge.BoundedExternalStageElementarity

/-!
# E 码语义与有限层初等性的等价

`textbookEZF` 只在正元数上精确表示公式满足关系。本模块先把初等性写成
“所有已认证正元 E 码的关系在层包含下绝对”，再利用一个未使用变量处理闭句，
证明它与量化全部外部 `Sigma_level` 公式的定义完全等价。
-/

namespace YesMetaZFC
namespace BMS
namespace ConstructibleBridge

open Constructible
open FiniteSequenceZF

/-- 层包含逐点作用于追加后的元组。 -/
theorem externalStageTuple_snoc_l
    {alpha beta : Ordinal} (hAlphaBeta : alpha <= beta)
    {arity : Nat} (assignment : Tuple (StageCarrier alpha) arity)
    (value : StageCarrier alpha) :
    externalStageTuple_l hAlphaBeta (snoc assignment value) =
      snoc (externalStageTuple_l hAlphaBeta assignment)
        (lStageInclusion hAlphaBeta value) := by
  funext index
  refine Fin.lastCases ?_ (fun prior => ?_) index
  · simp [externalStageTuple_l, snoc]
  · simp [externalStageTuple_l, snoc]

/-- 所有正元 `Sigma_level` E 关系在两个可构造层之间绝对。 -/
def ECodeSigmaElementaryAt_l
    (level : Nat) (alpha beta : Ordinal) : Prop :=
  exists (sourceNonempty : Nonempty (StageCarrier alpha))
      (targetNonempty : Nonempty (StageCarrier beta))
      (hAlphaBeta : alpha <= beta),
    forall {arity code : Nat},
      TextbookBoundedIsSigmaCode_l level (arity + 1) code ->
      forall assignment : Tuple (StageCarrier alpha) (arity + 1),
        textbookTupleGraph assignment ∈
            textbookEZF (LStageZF alpha) (natCode (arity + 1))
              (natCode code) <->
          textbookTupleGraph
              (externalStageTuple_l hAlphaBeta assignment) ∈
            textbookEZF (LStageZF beta) (natCode (arity + 1))
              (natCode code)

/-- 外部公式初等性推出所有认证 E 关系的绝对性。 -/
theorem eCodeSigmaElementaryAt_of_external_l
    {level : Nat} {alpha beta : Ordinal}
    (hElementary : BoundedExternalStageSigmaElementaryAt_l level alpha beta) :
    ECodeSigmaElementaryAt_l level alpha beta := by
  rcases hElementary with
    ⟨sourceNonempty, targetNonempty, hAlphaBeta, hElementary⟩
  refine ⟨sourceNonempty, targetNonempty, hAlphaBeta, ?_⟩
  intro arity code hCode assignment
  rcases hCode.decode with ⟨formula, hFormulaCode, hFormula⟩
  subst code
  rw [textbookTupleGraph_mem_compiledRelation_iff_l,
    textbookTupleGraph_mem_compiledRelation_iff_l]
  exact hElementary hFormula assignment

/-- 认证 E 关系的绝对性恢复量化全部外部有限层公式的初等性。 -/
theorem externalStageSigmaElementaryAt_of_eCode_l
    {level : Nat} {alpha beta : Ordinal}
    (hElementary : ECodeSigmaElementaryAt_l level alpha beta) :
    BoundedExternalStageSigmaElementaryAt_l level alpha beta := by
  rcases hElementary with
    ⟨sourceNonempty, targetNonempty, hAlphaBeta, hElementary⟩
  refine ⟨sourceNonempty, targetNonempty, hAlphaBeta, ?_⟩
  intro arity formula hFormula assignment
  cases arity with
  | zero =>
      let value : StageCarrier alpha := Classical.choice sourceNonempty
      have hPositive := hElementary
        (textbookFormulaCode_bounded_isSigma_l hFormula.weaken_l)
        (snoc assignment value)
      rw [textbookTupleGraph_mem_compiledRelation_iff_l,
        textbookTupleGraph_mem_compiledRelation_iff_l] at hPositive
      rw [FOFormula.satisfies_weaken,
        externalStageTuple_snoc_l,
        FOFormula.satisfies_weaken] at hPositive
      exact hPositive
  | succ arity =>
      have hPositive := hElementary
        (textbookFormulaCode_bounded_isSigma_l hFormula) assignment
      rw [textbookTupleGraph_mem_compiledRelation_iff_l,
        textbookTupleGraph_mem_compiledRelation_iff_l] at hPositive
      exact hPositive

/-- 两种有限层初等性表述完全等价。 -/
theorem eCodeSigmaElementaryAt_iff_external_l
    {level : Nat} {alpha beta : Ordinal} :
    ECodeSigmaElementaryAt_l level alpha beta <->
      BoundedExternalStageSigmaElementaryAt_l level alpha beta :=
  ⟨externalStageSigmaElementaryAt_of_eCode_l,
    eCodeSigmaElementaryAt_of_external_l⟩

end ConstructibleBridge
end BMS
end YesMetaZFC
