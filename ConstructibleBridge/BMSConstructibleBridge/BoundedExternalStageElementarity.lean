import BMSConstructibleBridge.ExternalBoundedLevyHierarchy
import BMSConstructibleBridge.ExternalStageElementarity

/-!
# 真正有界外部公式定义的层初等性

新版 YesMetaZFC 已把 bound 与 free 变量编码进公式类型。桥接层不再维护一套
把任意内在公式重新压平为旧 `Var` 编号的逆翻译；稳定关系直接量化依赖库的
有限元公式，并以 `ExternalBoundedIsSigmaFinite_l` 保留真正的有界量词底层。
这避免把无界存在量词误算成 `Delta0`，同时仍覆盖每个固定元数的全部公式。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible

/-- 用完整有界外部有限层定义 `L_alpha` 到 `L_beta` 的 `Sigma` 初等性。 -/
def BoundedExternalStageSigmaElementaryAt_l
    (level : Nat) (alpha beta : Ordinal.{u}) : Prop :=
  ∃ (sourceNonempty : Nonempty (StageCarrier alpha))
      (targetNonempty : Nonempty (StageCarrier beta))
      (hAlphaBeta : alpha ≤ beta),
    ∀ {arity : Nat} {formula : FOFormula arity},
      ExternalBoundedIsSigmaFinite_l level formula →
      ∀ assignment : Tuple (StageCarrier alpha) arity,
        FOFormula.Satisfies
            (fun left right : StageCarrier alpha => left.1 ∈ right.1)
            formula assignment ↔
          FOFormula.Satisfies
            (fun left right : StageCarrier beta => left.1 ∈ right.1)
            formula (externalStageTuple_l hAlphaBeta assignment)

/-- 完整有界外部有限层初等性随公式级别向下封闭。 -/
theorem BoundedExternalStageSigmaElementaryAt_mono_l
    {lowerLevel upperLevel : Nat} {alpha beta : Ordinal.{u}}
    (hLevels : lowerLevel ≤ upperLevel)
    (hElementary :
      BoundedExternalStageSigmaElementaryAt_l upperLevel alpha beta) :
    BoundedExternalStageSigmaElementaryAt_l lowerLevel alpha beta := by
  rcases hElementary with
    ⟨sourceNonempty, targetNonempty, hAlphaBeta, hElementary⟩
  refine ⟨sourceNonempty, targetNonempty, hAlphaBeta, ?_⟩
  intro arity formula hFormula assignment
  exact hElementary (hFormula.mono hLevels) assignment

/-- 完整有界外部有限层初等的层包含关系具有传递性。 -/
theorem BoundedExternalStageSigmaElementaryAt_trans_l
    {level : Nat} {alpha beta gamma : Ordinal.{u}}
    (hAlphaBeta :
      BoundedExternalStageSigmaElementaryAt_l level alpha beta)
    (hBetaGamma :
      BoundedExternalStageSigmaElementaryAt_l level beta gamma) :
    BoundedExternalStageSigmaElementaryAt_l level alpha gamma := by
  rcases hAlphaBeta with
    ⟨alphaNonempty, betaNonempty, hAlphaBeta, hElementaryAlphaBeta⟩
  rcases hBetaGamma with
    ⟨_betaNonempty, gammaNonempty, hBetaGamma, hElementaryBetaGamma⟩
  refine ⟨alphaNonempty, gammaNonempty, hAlphaBeta.trans hBetaGamma, ?_⟩
  intro arity formula hFormula assignment
  rw [hElementaryAlphaBeta hFormula assignment]
  rw [hElementaryBetaGamma hFormula
    (externalStageTuple_l hAlphaBeta assignment)]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge
