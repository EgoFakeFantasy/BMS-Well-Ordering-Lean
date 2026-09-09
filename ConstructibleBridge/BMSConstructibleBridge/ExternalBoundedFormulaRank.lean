import BMSConstructibleBridge.ExternalBoundedLevyHierarchy
import BMSConstructibleBridge.ExternalExistentialClosure
import BMSConstructibleBridge.TextbookLevyClassifierComplexity

/-!
# 任意外部公式的保守有界 Levy 秩

这里的秩只作工程上的有限上界，不把语义上的有界量词误认成零层。原子公式
作为真正的 `Delta0` 基底，其余结点按表面量词骨架递归，因此证书可由内核直接
核查，并可用于给固定的辅助公式统一预留常数复杂度。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible

/-- 表面递归秩同时给出真正有界外部层级中的 `Sigma`、`Pi` 证书。 -/
theorem externalBoundedFormula_rank_certificates_l {arity : Nat}
    (formula : FOFormula arity) :
    ExternalBoundedIsSigmaFinite_l (externalSigmaRank_l formula) formula ∧
      ExternalBoundedIsPiFinite_l (externalPiRank_l formula) formula := by
  induction formula with
  | mem left right =>
      exact ⟨.delta0 (.mem left right), .delta0 (.mem left right)⟩
  | eq left right =>
      exact ⟨.delta0 (.eq left right), .delta0 (.eq left right)⟩
  | neg body inductionHypothesis =>
      exact ⟨.neg inductionHypothesis.2, .neg inductionHypothesis.1⟩
  | conj left right leftHypothesis rightHypothesis =>
      exact ⟨
        .conj
          (leftHypothesis.1.mono (Nat.le_max_left _ _))
          (rightHypothesis.1.mono (Nat.le_max_right _ _)),
        .conj
          (leftHypothesis.2.mono (Nat.le_max_left _ _))
          (rightHypothesis.2.mono (Nat.le_max_right _ _))⟩
  | ex body inductionHypothesis =>
      have hExists : ExternalBoundedIsSigmaFinite_l
          (externalSigmaRank_l body) (.ex body) :=
        .ex inductionHypothesis.1
      exact ⟨hExists, .ofSigma hExists⟩

/-- 同时拥有同层 `Sigma` 与 `Pi` 证书。 -/
def ExternalBoundedIsBiFinite_l {arity : Nat}
    (level : Nat) (formula : FOFormula arity) : Prop :=
  ExternalBoundedIsSigmaFinite_l level formula ∧
    ExternalBoundedIsPiFinite_l level formula

/-- 每个固定外部公式都在某个有限等级上同时属于 `Sigma` 与 `Pi`。

这个存在性接口刻意隐藏表面递归秩。对很大的固定公式，后续只需使用所选的
有限等级，而无需反复归约整棵语法树。 -/
theorem exists_externalBoundedIsBiFinite_l {arity : Nat}
    (formula : FOFormula arity) :
    ∃ level, ExternalBoundedIsBiFinite_l level formula := by
  have hCertificates := externalBoundedFormula_rank_certificates_l formula
  exact ⟨max (externalSigmaRank_l formula) (externalPiRank_l formula),
    hCertificates.1.mono (Nat.le_max_left _ _),
    hCertificates.2.mono (Nat.le_max_right _ _)⟩

/-- 一个固定外部公式的共同有限复杂度等级。该选择只发生在 Lean 元层。 -/
noncomputable def externalBoundedBiLevel_l {arity : Nat}
    (formula : FOFormula arity) : Nat :=
  Classical.choose (exists_externalBoundedIsBiFinite_l formula)

/-- `externalBoundedBiLevel_l` 所选等级携带可核查的双侧复杂度证书。 -/
theorem externalBoundedBiLevel_spec_l {arity : Nat}
    (formula : FOFormula arity) :
    ExternalBoundedIsBiFinite_l (externalBoundedBiLevel_l formula) formula :=
  Classical.choose_spec (exists_externalBoundedIsBiFinite_l formula)

/-- 每个固定外部公式都属于某个真正有限的 `Sigma` 等级。 -/
theorem exists_externalBoundedIsSigmaFinite_l {arity : Nat}
    (formula : FOFormula arity) :
    ∃ level, ExternalBoundedIsSigmaFinite_l level formula :=
  ⟨externalSigmaRank_l formula,
    (externalBoundedFormula_rank_certificates_l formula).1⟩

/-- 一个固定外部公式的有限 `Sigma` 等级；选择只发生在 Lean 元层。 -/
noncomputable def externalBoundedSigmaLevel_l {arity : Nat}
    (formula : FOFormula arity) : Nat :=
  Classical.choose (exists_externalBoundedIsSigmaFinite_l formula)

/-- `externalBoundedSigmaLevel_l` 所选等级附带可核查的 `Sigma` 证书。 -/
theorem externalBoundedSigmaLevel_spec_l {arity : Nat}
    (formula : FOFormula arity) :
    ExternalBoundedIsSigmaFinite_l
      (externalBoundedSigmaLevel_l formula) formula :=
  Classical.choose_spec (exists_externalBoundedIsSigmaFinite_l formula)

theorem ExternalBoundedIsBiFinite_l.mono
    {arity lowerLevel upperLevel : Nat} {formula : FOFormula arity}
    (hFormula : ExternalBoundedIsBiFinite_l lowerLevel formula)
    (hLevels : lowerLevel ≤ upperLevel) :
    ExternalBoundedIsBiFinite_l upperLevel formula :=
  ⟨hFormula.1.mono hLevels, hFormula.2.mono hLevels⟩

theorem ExternalBoundedIsBiFinite_l.delta0
    {arity level : Nat} (formula : Delta0Formula arity) :
    ExternalBoundedIsBiFinite_l level formula.toFO :=
  ⟨.delta0 formula, .delta0 formula⟩

theorem ExternalBoundedIsBiFinite_l.neg
    {arity level : Nat} {formula : FOFormula arity}
    (hFormula : ExternalBoundedIsBiFinite_l level formula) :
    ExternalBoundedIsBiFinite_l level (.neg formula) :=
  ⟨.neg hFormula.2, .neg hFormula.1⟩

theorem ExternalBoundedIsBiFinite_l.conj
    {arity level : Nat} {left right : FOFormula arity}
    (hLeft : ExternalBoundedIsBiFinite_l level left)
    (hRight : ExternalBoundedIsBiFinite_l level right) :
    ExternalBoundedIsBiFinite_l level (.conj left right) :=
  ⟨.conj hLeft.1 hRight.1, .conj hLeft.2 hRight.2⟩

theorem ExternalBoundedIsBiFinite_l.disj
    {arity level : Nat} {left right : FOFormula arity}
    (hLeft : ExternalBoundedIsBiFinite_l level left)
    (hRight : ExternalBoundedIsBiFinite_l level right) :
    ExternalBoundedIsBiFinite_l level (FOFormula.disj left right) :=
  ⟨.disj hLeft.1 hRight.1, .disj hLeft.2 hRight.2⟩

theorem ExternalBoundedIsBiFinite_l.imp
    {arity level : Nat} {left right : FOFormula arity}
    (hLeft : ExternalBoundedIsBiFinite_l level left)
    (hRight : ExternalBoundedIsBiFinite_l level right) :
    ExternalBoundedIsBiFinite_l level (FOFormula.imp left right) :=
  ⟨.imp hLeft.2 hRight.1, .imp hLeft.1 hRight.2⟩

theorem ExternalBoundedIsBiFinite_l.biimp
    {arity level : Nat} {left right : FOFormula arity}
    (hLeft : ExternalBoundedIsBiFinite_l level left)
    (hRight : ExternalBoundedIsBiFinite_l level right) :
    ExternalBoundedIsBiFinite_l level (FOFormula.biimp left right) := by
  rw [FOFormula.biimp]
  exact (hLeft.imp hRight).conj (hRight.imp hLeft)

theorem ExternalBoundedIsBiFinite_l.rename
    {arity targetArity level : Nat} {formula : FOFormula arity}
    (hFormula : ExternalBoundedIsBiFinite_l level formula)
    (rename : Fin arity → Fin targetArity) :
    ExternalBoundedIsBiFinite_l level (formula.rename rename) :=
  ⟨hFormula.1.rename rename, hFormula.2.rename rename⟩

theorem ExternalBoundedIsBiFinite_l.ex
    {arity level : Nat} {formula : FOFormula (arity + 1)}
    (hFormula : ExternalBoundedIsBiFinite_l level formula) :
    ExternalBoundedIsBiFinite_l (level + 1) (.ex formula) := by
  have hExists : ExternalBoundedIsSigmaFinite_l level (.ex formula) :=
    .ex hFormula.1
  exact ⟨hExists.mono (Nat.le_succ level), .ofSigma hExists⟩

theorem ExternalBoundedIsBiFinite_l.all
    {arity level : Nat} {formula : FOFormula (arity + 1)}
    (hFormula : ExternalBoundedIsBiFinite_l level formula) :
    ExternalBoundedIsBiFinite_l (level + 1) (.all formula) := by
  have hAll : ExternalBoundedIsPiFinite_l level (.all formula) :=
    .all hFormula.2
  exact ⟨.ofPi hAll, hAll.mono (Nat.le_succ level)⟩

/-- 一个或多个无界存在量词只使双侧共同上界上升一层。 -/
theorem externalExistentialClosure_isBiFinite_l
    {arity level count : Nat} {formula : FOFormula (arity + count)}
    (hFormula : ExternalBoundedIsBiFinite_l level formula) :
    ExternalBoundedIsBiFinite_l (level + 1)
      (externalExistentialClosure_l count formula) := by
  constructor
  · exact (externalExistentialClosure_isSigmaFinite_l count formula
      hFormula.1).mono (Nat.le_succ level)
  · exact .ofSigma
      (externalExistentialClosure_isSigmaFinite_l count formula hFormula.1)

end YesMetaZFC.BMS.ConstructibleBridge
