import BMSConstructibleBridge.TextbookLevyClassifierFormula

/-!
# 有限 Lévy 分类器的可核查复杂度上界

本文件不把有限计算性误当成 `Delta0`。它直接递归读取外部公式的量词骨架，
同时计算一个 `Sigma` 上界和一个 `Pi` 上界，并为两个数值各自产生正式证书。
这给当前分类器提供诚实的基线；后续证书化改写必须把公开分类器降到
一个无界存在块之后只剩真正有界公式的形状。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible
open Logic FirstOrder StabilityFrame

mutual
  /-- 外部成员公式作为累积 `Sigma` 公式所需的结构递归上界。 -/
  def externalSigmaRank_l : {arity : Nat} → FOFormula arity → Nat
    | _, .mem _ _ => 0
    | _, .eq _ _ => 0
    | _, .neg body => externalPiRank_l body
    | _, .conj left right =>
        max (externalSigmaRank_l left) (externalSigmaRank_l right)
    | _, .ex body => externalSigmaRank_l body

  /-- 外部成员公式作为累积 `Pi` 公式所需的结构递归上界。 -/
  def externalPiRank_l : {arity : Nat} → FOFormula arity → Nat
    | _, .mem _ _ => 0
    | _, .eq _ _ => 0
    | _, .neg body => externalSigmaRank_l body
    | _, .conj left right =>
        max (externalPiRank_l left) (externalPiRank_l right)
    | _, .ex body => externalSigmaRank_l body + 1
end

/-- 外部变量改名不改变递归计算出的两个 Lévy 秩。 -/
theorem externalRanks_rename_l {arity targetArity : Nat}
    (formula : FOFormula arity) (rename : Fin arity → Fin targetArity) :
    externalSigmaRank_l (FOFormula.rename rename formula) =
        externalSigmaRank_l formula ∧
      externalPiRank_l (FOFormula.rename rename formula) =
        externalPiRank_l formula := by
  induction formula generalizing targetArity with
  | mem left right => exact ⟨rfl, rfl⟩
  | eq left right => exact ⟨rfl, rfl⟩
  | neg body inductionHypothesis =>
      exact ⟨(inductionHypothesis rename).2,
        (inductionHypothesis rename).1⟩
  | conj left right leftHypothesis rightHypothesis =>
      constructor
      · simp only [FOFormula.rename, externalSigmaRank_l,
          (leftHypothesis rename).1, (rightHypothesis rename).1]
      · simp only [FOFormula.rename, externalPiRank_l,
          (leftHypothesis rename).2, (rightHypothesis rename).2]
  | ex body inductionHypothesis =>
      exact ⟨(inductionHypothesis (FOFormula.liftRename rename)).1,
        congrArg (· + 1)
          (inductionHypothesis (FOFormula.liftRename rename)).1⟩

/-- 外部变量改名保持递归 `Sigma` 秩。 -/
@[simp]
theorem externalSigmaRank_rename_l {arity targetArity : Nat}
    (formula : FOFormula arity) (rename : Fin arity → Fin targetArity) :
    externalSigmaRank_l (FOFormula.rename rename formula) =
      externalSigmaRank_l formula :=
  (externalRanks_rename_l formula rename).1

/-- 外部变量改名保持递归 `Pi` 秩。 -/
@[simp]
theorem externalPiRank_rename_l {arity targetArity : Nat}
    (formula : FOFormula arity) (rename : Fin arity → Fin targetArity) :
    externalPiRank_l (FOFormula.rename rename formula) =
      externalPiRank_l formula :=
  (externalRanks_rename_l formula rename).2

/-- 递归计算出的两个上界分别带有真实的外部有限 Lévy 证书。 -/
theorem externalFormula_rank_certificates_l {arity : Nat}
    (formula : FOFormula arity) :
    ExternalIsSigmaFinite (externalSigmaRank_l formula) formula ∧
      ExternalIsPiFinite (externalPiRank_l formula) formula := by
  induction formula with
  | mem left right => exact ⟨.mem left right, .mem left right⟩
  | eq left right => exact ⟨.eq left right, .eq left right⟩
  | neg body inductionHypothesis =>
      exact ⟨.neg inductionHypothesis.2, .neg inductionHypothesis.1⟩
  | conj left right leftHypothesis rightHypothesis =>
      exact ⟨
        .conj
          (leftHypothesis.1.mono_l (Nat.le_max_left _ _))
          (rightHypothesis.1.mono_l (Nat.le_max_right _ _)),
        .conj
          (leftHypothesis.2.mono_l (Nat.le_max_left _ _))
          (rightHypothesis.2.mono_l (Nat.le_max_right _ _))⟩
  | ex body inductionHypothesis =>
      have hExists : ExternalIsSigmaFinite
          (externalSigmaRank_l body) (.ex body) :=
        .ex inductionHypothesis.1
      exact ⟨hExists, .ofSigma hExists⟩

/-- 当前五元分类器具有由其实际语法树计算出的外部 `Sigma` 证书。 -/
theorem textbookLevyClassifierFormula_isSigmaRank_l :
    ExternalIsSigmaFinite
      (externalSigmaRank_l textbookLevyClassifierFormula_l)
      textbookLevyClassifierFormula_l :=
  (externalFormula_rank_certificates_l textbookLevyClassifierFormula_l).1

/-- 同一复杂度证书经语法桥得到 YesMetaZFC 原生成员语言证书。 -/
theorem translatedTextbookLevyClassifierFormula_isSigmaRank_l :
    Formula.IsSigmaFinite membershipLevyBound
      (externalSigmaRank_l textbookLevyClassifierFormula_l)
      (translateExternalFormula textbookLevyClassifierFormula_l) :=
  translateExternalFormula_isSigmaFinite_l
    textbookLevyClassifierFormula_isSigmaRank_l

end YesMetaZFC.BMS.ConstructibleBridge
