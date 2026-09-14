import BMSConstructibleBridge.StageStableToUniverseSyntax
import BMSConstructibleBridge.StageStableBetweenSyntax
import BMSConstructibleBridge.ExternalBoundedFormulaRank

/-!
# 可计算的有限反射等级预算

直接读取实际公式的有限语法秩，不使用旧预算中的 `Classical.choose`。
具名层公式的数码仍按有界语法处理，所以其统一界不随数码增长；ambient 公式
则按实际生成的语法树计算。这里不改变旧稳定关系，也不宣称两种预算逐值相等。
这些证书只解决有效构造中的复杂度义务，不是对象理论反射定理或证明码生成器。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.EffectiveStability

open Constructible

set_option autoImplicit false

/-- 实际语法树的可计算双侧秩。 -/
def rank_m {n : Nat} (φ : FOFormula n) : Nat :=
  max (externalSigmaRank_l φ) (externalPiRank_l φ)

theorem rank_spec_m {n : Nat} (φ : FOFormula n) :
    ExternalBoundedIsBiFinite_l (rank_m φ) φ :=
  ⟨(externalBoundedFormula_rank_certificates_l φ).1.mono (Nat.le_max_left _ _),
    (externalBoundedFormula_rank_certificates_l φ).2.mono (Nat.le_max_right _ _)⟩

/-- 四个固定非有界子式的共同语法界；不包含可变数码。 -/
def base_m : Nat :=
  max (rank_m (Constructible.Model.omegaSetAt (2 : Fin 5))) <|
  max (rank_m textbookEStageLevelAgreementBody_l) <|
  max (rank_m (Constructible.Model.omegaSetAt (4 : Fin 5)))
    (rank_m localLStagePairFormula_l)

private theorem parts :
    ExternalBoundedIsBiFinite_l base_m (Constructible.Model.omegaSetAt (2 : Fin 5)) ∧
    ExternalBoundedIsBiFinite_l base_m textbookEStageLevelAgreementBody_l ∧
    ExternalBoundedIsBiFinite_l base_m (Constructible.Model.omegaSetAt (4 : Fin 5)) ∧
    ExternalBoundedIsBiFinite_l base_m localLStagePairFormula_l := by
  refine ⟨(rank_spec_m _).mono ?_, (rank_spec_m _).mono ?_,
    (rank_spec_m _).mono ?_, (rank_spec_m _).mono ?_⟩
  · exact Nat.le_max_left _ _
  · exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  · exact (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  · exact (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)

private theorem agreement (b k : Nat)
    (h₀ : ExternalBoundedIsBiFinite_l b (Constructible.Model.omegaSetAt (2 : Fin 5)))
    (h₁ : ExternalBoundedIsBiFinite_l b textbookEStageLevelAgreementBody_l) :
    ExternalBoundedIsSigmaFinite_l (b + 2)
      (textbookEStageLevelAgreementFormula_l k) := by
  have h : ExternalBoundedIsSigmaFinite_l (b + 2)
      (textbookEStageLevelAgreementCore_l k) := by
    rw [textbookEStageLevelAgreementCore_l]
    exact (h₀.1.mono (Nat.le_add_right _ _)).conj <|
      (ExternalBoundedIsSigmaFinite_l.delta0
        (level := b + 2) (Delta0Formula.natLiteralDeltaAt 1 (3 : Fin 5))).conj <|
      (ExternalBoundedIsSigmaFinite_l.delta0
        (level := b + 2) (Delta0Formula.natLiteralDeltaAt k (4 : Fin 5))).conj
        h₁.all.all.1
  rw [textbookEStageLevelAgreementFormula_l]
  exact .ex (.ex (.ex h))

/-- 两个具名层的公式具有与等级数码无关的可计算界。 -/
theorem agreement_m (k : Nat) :
    ExternalBoundedIsSigmaFinite_l (base_m + 2)
      (textbookEStageLevelAgreementFormula_l k) :=
  agreement base_m k parts.1 parts.2.1

/-- 稳定边的具名层公式统一落在零级预算内。 -/
theorem between_m (k : Nat) :
    ExternalBoundedIsSigmaFinite_l (base_m + 2)
      (stageStableBetweenFormulaAtLevel_l k) := by
  have h : ExternalBoundedIsSigmaFinite_l (base_m + 2)
      (stageStableBetweenCoreAtLevel_l k) := by
    rw [stageStableBetweenCoreAtLevel_l]
    exact (parts.2.2.1.1.mono (Nat.le_add_right _ _)).conj <|
      (ExternalBoundedIsSigmaFinite_l.delta0
        (level := base_m + 2) (Delta0Formula.mem (4 : Fin 5) (0 : Fin 5))).conj <|
      (ExternalBoundedIsSigmaFinite_l.delta0
        (level := base_m + 2) (Delta0Formula.mem (0 : Fin 5) (1 : Fin 5))).conj <|
      (ExternalBoundedIsSigmaFinite_l.delta0
        (level := base_m + 2) (stageIsSuccLimitDeltaAt_l (0 : Fin 5))).conj <|
      (ExternalBoundedIsSigmaFinite_l.delta0
        (level := base_m + 2) (stageIsSuccLimitDeltaAt_l (1 : Fin 5))).conj <|
      (ExternalBoundedIsSigmaFinite_l.delta0
        (level := base_m + 2) (Delta0Formula.mem (2 : Fin 5) (3 : Fin 5))).conj <|
      (parts.2.2.2.1.rename ![(1 : Fin 5), 3] |>.mono (Nat.le_add_right _ _)).conj <|
      ((ExternalBoundedIsSigmaFinite_l.delta0
        (level := base_m + 2) relativizedLocalLStagePairDelta_l).rename
        ![(3 : Fin 5), 0, 2]).conj ((agreement_m k).rename ![(2 : Fin 5), 3])
  rw [stageStableBetweenFormulaAtLevel_l]
  exact externalExistentialClosure_isSigmaFinite_l 3 _ h

private def schedule (b : Nat) : Nat → Nat
  | 0 => b
  | k + 1 => max (schedule b k + 1)
      (externalSigmaRank_l (stageStableToUniverseFormulaAtLevel_l (schedule b k)))

private theorem grow (b k : Nat) : schedule b k < schedule b (k + 1) :=
  (Nat.lt_succ_self _).trans_le (Nat.le_max_left _ _)

private theorem bound (b k : Nat) : b ≤ schedule b k := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k h => exact h.trans (grow b k).le

/-- 后继预算严格增长，并吸收前一级实际 ambient 公式的语法秩。
    初值作为递归参数保留，核验不必计算巨型固定公式的具体秩。 -/
def level_m : Nat → Nat := schedule (base_m + 2)

theorem lt_succ_m (k : Nat) : level_m k < level_m (k + 1) :=
  grow _ k

theorem mono_m {j k : Nat} (h : j ≤ k) : level_m j ≤ level_m k := by
  induction h with
  | refl => exact Nat.le_refl _
  | @step k _ h => exact h.trans (lt_succ_m k).le

/-- ambient 公式的秩确实被下一预算吸收，不假设复杂度控制。 -/
theorem ambient_succ_m (k : Nat) :
    ExternalBoundedIsSigmaFinite_l (level_m (k + 1))
      (stageStableToUniverseFormulaAtLevel_l (level_m k)) :=
  (externalBoundedFormula_rank_certificates_l _).1.mono (Nat.le_max_right _ _)

/-- 合法输入只在 `j < k` 时要求向下端点反射 ambient 稳定边。 -/
theorem ambient_m {j k : Nat} (h : j < k) :
    ExternalBoundedIsSigmaFinite_l (level_m k)
      (stageStableToUniverseFormulaAtLevel_l (level_m j)) :=
  (ambient_succ_m j).mono (mono_m (Nat.succ_le_iff.mpr h))

theorem named_m (j k : Nat) :
    ExternalBoundedIsSigmaFinite_l (level_m k)
      (stageStableBetweenFormulaAtLevel_l (level_m j)) :=
  (between_m (level_m j)).mono (bound _ k)

/-- 任意有限上方图的存在闭包不增加 `Sigma` 等级。 -/
theorem close_m {n c k : Nat} {φ : FOFormula (n + c)}
    (h : ExternalBoundedIsSigmaFinite_l (level_m k) φ) :
    ExternalBoundedIsSigmaFinite_l (level_m k) (externalExistentialClosure_l c φ) :=
  externalExistentialClosure_isSigmaFinite_l c φ h

end YesMetaZFC.BMS.ConstructibleBridge.EffectiveStability
