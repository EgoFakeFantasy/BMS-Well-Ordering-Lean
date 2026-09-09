import BMSConstructibleBridge.ExternalLevyHierarchy

/-!
# 由外部成员公式刻画的可构造层初等性

外部 `FOFormula` 与 `LStageZF` 来自同一可构造宇宙库，因而这一接口适合直接
连接规范 E 码。它量化全部固定元数的 `Sigma_level` 公式，而不是某个有限公式
片段；后续 Tarski--Vaught 编码将把这个量化改写为单一对象语言公式。
-/

namespace YesMetaZFC
namespace BMS
namespace ConstructibleBridge

open Constructible

/-- 沿 `L_alpha` 到 `L_beta` 的包含映射提升一个有限元组。 -/
def externalStageTuple_l
    {alpha beta : Ordinal} (hAlphaBeta : alpha <= beta) {arity : Nat}
    (assignment : Tuple (StageCarrier alpha) arity) :
    Tuple (StageCarrier beta) arity :=
  fun index => lStageInclusion hAlphaBeta (assignment index)

/-- 用外部纯成员公式定义固定有限 `Sigma` 层的可构造层初等性。 -/
def ExternalStageSigmaElementaryAt_l
    (level : Nat) (alpha beta : Ordinal) : Prop :=
  exists (sourceNonempty : Nonempty (StageCarrier alpha))
      (targetNonempty : Nonempty (StageCarrier beta))
      (hAlphaBeta : alpha <= beta),
    forall {arity : Nat} {formula : FOFormula arity},
      ExternalIsSigmaFinite level formula ->
      forall assignment : Tuple (StageCarrier alpha) arity,
        FOFormula.Satisfies
            (fun left right : StageCarrier alpha => left.1 ∈ right.1)
            formula assignment <->
          FOFormula.Satisfies
            (fun left right : StageCarrier beta => left.1 ∈ right.1)
            formula (externalStageTuple_l hAlphaBeta assignment)

/-- 外部有限 `Sigma` 初等性随公式层级向下封闭。 -/
theorem ExternalStageSigmaElementaryAt_mono_l
    {lowerLevel upperLevel : Nat} {alpha beta : Ordinal}
    (hLevels : lowerLevel <= upperLevel)
    (hElementary : ExternalStageSigmaElementaryAt_l upperLevel alpha beta) :
    ExternalStageSigmaElementaryAt_l lowerLevel alpha beta := by
  rcases hElementary with
    ⟨sourceNonempty, targetNonempty, hAlphaBeta, hElementary⟩
  refine ⟨sourceNonempty, targetNonempty, hAlphaBeta, ?_⟩
  intro arity formula hFormula assignment
  exact hElementary (hFormula.mono_l hLevels) assignment

/-- 外部有限 `Sigma` 初等的层包含关系具有传递性。 -/
theorem ExternalStageSigmaElementaryAt_trans_l
    {level : Nat} {alpha beta gamma : Ordinal}
    (hAlphaBeta : ExternalStageSigmaElementaryAt_l level alpha beta)
    (hBetaGamma : ExternalStageSigmaElementaryAt_l level beta gamma) :
    ExternalStageSigmaElementaryAt_l level alpha gamma := by
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

end ConstructibleBridge
end BMS
end YesMetaZFC
