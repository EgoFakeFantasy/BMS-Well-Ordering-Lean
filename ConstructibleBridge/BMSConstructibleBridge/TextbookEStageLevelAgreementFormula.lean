import BMSConstructibleBridge.TextbookEStageAgreementFormula
import BMSConstructibleBridge.TextbookEAgreementFormula
import BMSConstructibleBridge.TextbookBoundedLevyClassifierBounded
import ConstructibleUniverse.SetTheory.ZFC.Constructible.CondensationFixedParameters

/-!
# 后继极限层中的统一有限层 E 一致性

本文件把单个公式码上的 `textbookEStageAgreementFormula_l` 与真正有界的
Lévy 分类器组合。在外层 `L_top` 中，右端集合 `B = L_β` 同时充当分类器的
量词界；因此公式码分类仍是 `Delta0`，而 E 值由外层后继极限层实际承载。

这只比较两个已经命名的集合大小结构。它实现 Hunter 证明中的 `φ₁` 原子，
不把右端集合偷换成 ambient 构造宇宙，因而不声称解决 `φ₂`。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible
open Constructible.FiniteSequenceZF

noncomputable section

set_option maxHeartbeats 800000

/-!
七元布局为 `[A,B,omega,sigmaCode,levelCode,arity,code]`。分类器以 `B` 为
显式量词界；结论比较 `A`、`B` 上对应 E 关系。
-/

/-- 统一有限层 E 一致性的七元量词体。 -/
def textbookEStageLevelAgreementBody_l : FOFormula 7 :=
  FOFormula.imp
    (.mem (5 : Fin 7) (2 : Fin 7)) <|
  FOFormula.imp
    (.mem (6 : Fin 7) (2 : Fin 7)) <|
  FOFormula.imp
    (FOFormula.ex (.mem (7 : Fin 8) (5 : Fin 8))) <|
  FOFormula.imp
    (FOFormula.rename ![1, 2, 3, 4, 5, 6]
      boundedTextbookBoundedLevyClassifierDelta_l.toFO)
    (FOFormula.rename ![0, 1, 5, 6]
      textbookEStageAgreementFormula_l)

/-- 固定辅助常量后，对全部标准自然数元数和公式码作比较。 -/
def textbookEStageLevelAgreementCore_l (level : Nat) : FOFormula 5 :=
  .conj
    (Constructible.Model.omegaSetAt (2 : Fin 5))
    (.conj
      (Delta0Formula.natLiteralDeltaAt 1 (3 : Fin 5)).toFO
      (.conj
        (Delta0Formula.natLiteralDeltaAt level (4 : Fin 5)).toFO
        (FOFormula.all <| FOFormula.all
          textbookEStageLevelAgreementBody_l)))

/-- 两个公开集合参数上的统一有限层 E 一致性公式。 -/
def textbookEStageLevelAgreementFormula_l (level : Nat) : FOFormula 2 :=
  .ex <| .ex <| .ex <| textbookEStageLevelAgreementCore_l level

/-- 七元体中的有界分类器精确识别标准 `Sigma_level` 公式码。 -/
theorem satisfiesIn_textbookEStageLevelClassifier_iff_l
    {top β : Ordinal.{u}} (hβtop : β < top)
    (hβ : Order.IsSuccLimit β) (hωβ : Ordinal.omega0 < β)
    (level arity code : Nat) {A B : ZFSet.{u}}
    (hA : A ∈ LStageZF top) (hB : B ∈ LStageZF top)
    (hBValue : B = LStageZF β) :
    Constructible.Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        (FOFormula.rename ![1, 2, 3, 4, 5, 6]
          boundedTextbookBoundedLevyClassifierDelta_l.toFO)
        ![A, B, Ordinal.omega0.toZFSet, natCode 1,
          natCode level, natCode arity, natCode code] ↔
      TextbookBoundedIsSigmaCode_l level arity code := by
  rw [Constructible.Model.satisfiesIn_rename]
  have hAssignment :
      (fun position =>
        ![A, B, Ordinal.omega0.toZFSet, natCode 1,
          natCode level, natCode arity, natCode code]
          (![1, 2, 3, 4, 5, 6] position)) =
        tupleCons (LStageZF β)
          (Delta0Formula.val
            (textbookBoundedLevyClassifierStageAssignment_l β hωβ
              (textbookSigmaJudgment_l level arity code))) := by
    rw [textbookBoundedLevyClassifierStageAssignment_value_l]
    funext position
    fin_cases position
    · exact hBValue
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  rw [hAssignment]
  exact (satisfiesIn_boundedTextbookBoundedLevyClassifier_iff_l
    hβtop hβ hωβ (textbookSigmaJudgment_l level arity code)).trans
      (by simp [textbookSigmaJudgment_l,
        TextbookBoundedLevyJudgment.Certified])

/--
标准辅助常量下的核心公式精确比较 `A`、`B` 上所有有限层 E 关系。
-/
theorem satisfiesIn_textbookEStageLevelAgreementCore_iff_l
    {top β : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hωTop : Ordinal.omega0 < top) (hβtop : β < top)
    (hβ : Order.IsSuccLimit β) (hωβ : Ordinal.omega0 < β)
    (level : Nat) {A B : ZFSet.{u}}
    (hA : A ∈ LStageZF top) (hB : B ∈ LStageZF top)
    (hBValue : B = LStageZF β) :
    Constructible.Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        (textbookEStageLevelAgreementCore_l level)
        ![A, B, Ordinal.omega0.toZFSet, natCode 1, natCode level] ↔
      TextbookELevelAgreement_l level
        ⟨A, ⟨top, hA⟩⟩
        ⟨B, ⟨top, hB⟩⟩ := by
  let fixedAssignment : Tuple ZFSet.{u} 5 :=
    ![A, B, Ordinal.omega0.toZFSet, natCode 1, natCode level]
  have hFixedAssignment : ∀ position,
      fixedAssignment position ∈ LStageZF top := by
    intro position
    fin_cases position
    · exact hA
    · exact hB
    · exact omega_toZFSet_mem_stage_l hωTop
    · exact natCode_mem_stage_l hωTop 1
    · exact natCode_mem_stage_l hωTop level
  change Constructible.Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
      (textbookEStageLevelAgreementCore_l level) fixedAssignment ↔ _
  simp only [textbookEStageLevelAgreementCore_l,
    Constructible.Model.SatisfiesIn]
  rw [Constructible.Model.satisfiesIn_omegaSetAt_iff hTop hωTop
      (2 : Fin 5) fixedAssignment hFixedAssignment,
    satisfiesIn_natLiteralDeltaAt_stage_iff_l 1 (3 : Fin 5)
      fixedAssignment hFixedAssignment,
    satisfiesIn_natLiteralDeltaAt_stage_iff_l level (4 : Fin 5)
      fixedAssignment hFixedAssignment,
    satisfiesIn_all_stage_iff_l]
  dsimp [fixedAssignment]
  simp only [true_and]
  constructor
  · intro hAll
    intro positiveArity code hCode tuple hTuple
    let arity := positiveArity + 1
    have hArityStage : natCode arity ∈ LStageZF top :=
      natCode_mem_stage_l hωTop arity
    have hCodeStage : natCode code ∈ LStageZF top :=
      natCode_mem_stage_l hωTop code
    have hInner := hAll (natCode arity) hArityStage
    have hBody := (satisfiesIn_all_stage_iff_l
      (LStageZF top : Set ZFSet.{u})
      textbookEStageLevelAgreementBody_l
      (snoc ![A, B, Ordinal.omega0.toZFSet, natCode 1, natCode level]
        (natCode arity))).mp hInner (natCode code) hCodeStage
    have hSnoc :
        snoc (snoc
          ![A, B, Ordinal.omega0.toZFSet, natCode 1, natCode level]
          (natCode arity)) (natCode code) =
        ![A, B, Ordinal.omega0.toZFSet, natCode 1, natCode level,
          natCode arity, natCode code] := by
      funext position
      fin_cases position <;> rfl
    rw [hSnoc] at hBody
    simp only [textbookEStageLevelAgreementBody_l,
      Constructible.Model.satisfiesIn_imp_iff] at hBody
    have hArityOmega : natCode arity ∈ Ordinal.omega0.toZFSet :=
      (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode arity)).mpr ⟨arity, rfl⟩
    have hCodeOmega : natCode code ∈ Ordinal.omega0.toZFSet :=
      (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode code)).mpr ⟨code, rfl⟩
    have hPositive : ∃ member : ZFSet.{u},
        member ∈ LStageZF top ∧ member ∈ natCode arity :=
      ⟨natCode 0, natCode_mem_stage_l hωTop 0,
        (IndexedSequenceZF.mem_natCode_iff_exists_lt
          (natCode 0) arity).mpr
            ⟨0, Nat.zero_lt_succ positiveArity, rfl⟩⟩
    have hClassifier :=
      (satisfiesIn_textbookEStageLevelClassifier_iff_l
        hβtop hβ hωβ level arity code hA hB hBValue).mpr hCode
    have hAgreement := hBody hArityOmega hCodeOmega hPositive hClassifier
    have hAgreement' :
        Constructible.Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
          textbookEStageAgreementFormula_l
          ![A, B, natCode arity, natCode code] := by
      rw [Constructible.Model.satisfiesIn_rename] at hAgreement
      have hSelected :
          (fun position =>
            ![A, B, Ordinal.omega0.toZFSet, natCode 1, natCode level,
              natCode arity, natCode code]
              (![0, 1, 5, 6] position)) =
            ![A, B, natCode arity, natCode code] := by
        funext position
        fin_cases position <;> rfl
      rw [hSelected] at hAgreement
      exact hAgreement
    have hTupleValue : tuple.1 ∈ textbookTupleSpace A arity := hTuple
    exact (satisfiesIn_textbookEStageAgreementFormula_natCode_iff_l
      hTop hωTop arity code hA hB).mp hAgreement' tuple.1 hTupleValue
  · intro hAgreement
    intro arityValue hArityStage
    apply (satisfiesIn_all_stage_iff_l
      (LStageZF top : Set ZFSet.{u})
      textbookEStageLevelAgreementBody_l
      (snoc ![A, B, Ordinal.omega0.toZFSet, natCode 1, natCode level]
        arityValue)).mpr
    intro codeValue hCodeStage
    have hSnoc :
        snoc (snoc
          ![A, B, Ordinal.omega0.toZFSet, natCode 1, natCode level]
          arityValue) codeValue =
        ![A, B, Ordinal.omega0.toZFSet, natCode 1, natCode level,
          arityValue, codeValue] := by
      funext position
      fin_cases position <;> rfl
    rw [hSnoc]
    simp only [textbookEStageLevelAgreementBody_l,
      Constructible.Model.satisfiesIn_imp_iff]
    intro hArityOmega hCodeOmega hPositive hClassifier
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode
      arityValue).mp hArityOmega with ⟨arity, rfl⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode
      codeValue).mp hCodeOmega with ⟨code, rfl⟩
    cases arity with
    | zero =>
        rcases hPositive with ⟨member, _hMemberStage, hMember⟩
        exfalso
        change member ∈ (natCode 0 : ZFSet.{u}) at hMember
        simpa using hMember
    | succ positiveArity =>
        have hCertified : TextbookBoundedIsSigmaCode_l level
            (positiveArity + 1) code := by
          apply (satisfiesIn_textbookEStageLevelClassifier_iff_l
            hβtop hβ hωβ level (positiveArity + 1) code
              hA hB hBValue).mp
          simpa only [Nat.succ_eq_add_one] using hClassifier
        apply (Constructible.Model.satisfiesIn_rename
          (LStageZF top : Set ZFSet.{u})
          textbookEStageAgreementFormula_l ![0, 1, 5, 6]
          ![A, B, Ordinal.omega0.toZFSet, natCode 1, natCode level,
            natCode (positiveArity + 1), natCode code]).mpr
        have hSelected :
            (fun position =>
              ![A, B, Ordinal.omega0.toZFSet, natCode 1, natCode level,
                natCode (positiveArity + 1), natCode code]
                (![0, 1, 5, 6] position)) =
              ![A, B, natCode (positiveArity + 1), natCode code] := by
          funext position
          fin_cases position <;> rfl
        rw [hSelected]
        apply (satisfiesIn_textbookEStageAgreementFormula_natCode_iff_l
          hTop hωTop (positiveArity + 1) code hA hB).mpr
        intro tuple hTuple
        exact hAgreement positiveArity code hCertified
          ⟨tuple, ⟨top,
            (LStageZF_isTransitive top).mem_trans hTuple
              (textbookTupleSpace_mem_LStageZF_l
                hTop hA (positiveArity + 1))⟩⟩ hTuple

/-- 公开二元公式在后继极限层中精确表达统一有限层 E 一致性。 -/
theorem satisfiesIn_textbookEStageLevelAgreementFormula_iff_l
    {top β : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hωTop : Ordinal.omega0 < top) (hβtop : β < top)
    (hβ : Order.IsSuccLimit β) (hωβ : Ordinal.omega0 < β)
    (level : Nat) {A B : ZFSet.{u}}
    (hA : A ∈ LStageZF top) (hB : B ∈ LStageZF top)
    (hBValue : B = LStageZF β) :
    Constructible.Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        (textbookEStageLevelAgreementFormula_l level) ![A, B] ↔
      TextbookELevelAgreement_l level
        ⟨A, ⟨top, hA⟩⟩ ⟨B, ⟨top, hB⟩⟩ := by
  simp only [textbookEStageLevelAgreementFormula_l,
    Constructible.Model.SatisfiesIn]
  constructor
  · rintro ⟨omegaValue, hOmegaStage, sigmaValue, hSigmaStage,
      levelValue, hLevelStage, hCore⟩
    have hAssignment :
        snoc (snoc (snoc ![A, B] omegaValue) sigmaValue) levelValue =
          ![A, B, omegaValue, sigmaValue, levelValue] := by
      funext position
      fin_cases position <;> rfl
    rw [hAssignment] at hCore
    have hFullAssignment : ∀ position : Fin 5,
        ![A, B, omegaValue, sigmaValue, levelValue] position ∈
          LStageZF top := by
      intro position
      fin_cases position <;> assumption
    have hCoreParts := hCore
    simp only [textbookEStageLevelAgreementCore_l,
      Constructible.Model.SatisfiesIn] at hCoreParts
    rcases hCoreParts with ⟨hOmegaFormula, hSigmaFormula,
      hLevelFormula, hRest⟩
    have hOmegaValue : omegaValue = Ordinal.omega0.toZFSet :=
      (Constructible.Model.satisfiesIn_omegaSetAt_iff
        hTop hωTop (2 : Fin 5)
        ![A, B, omegaValue, sigmaValue, levelValue]
        hFullAssignment).mp hOmegaFormula
    have hSigmaValue : sigmaValue = natCode 1 :=
      (satisfiesIn_natLiteralDeltaAt_stage_iff_l
        1 (3 : Fin 5) ![A, B, omegaValue, sigmaValue, levelValue]
        hFullAssignment).mp hSigmaFormula
    have hLevelValue : levelValue = natCode level :=
      (satisfiesIn_natLiteralDeltaAt_stage_iff_l
        level (4 : Fin 5) ![A, B, omegaValue, sigmaValue, levelValue]
        hFullAssignment).mp hLevelFormula
    subst omegaValue
    subst sigmaValue
    subst levelValue
    apply (satisfiesIn_textbookEStageLevelAgreementCore_iff_l
      hTop hωTop hβtop hβ hωβ level hA hB hBValue).mp
    simpa only [textbookEStageLevelAgreementCore_l,
      Constructible.Model.SatisfiesIn] using
      (show Constructible.Model.SatisfiesIn
        (LStageZF top : Set ZFSet.{u})
        (textbookEStageLevelAgreementCore_l level)
        ![A, B, Ordinal.omega0.toZFSet, natCode 1, natCode level] from
          ⟨hOmegaFormula, hSigmaFormula, hLevelFormula, hRest⟩)
  · intro hAgreement
    refine ⟨Ordinal.omega0.toZFSet, omega_toZFSet_mem_stage_l hωTop,
      natCode 1, natCode_mem_stage_l hωTop 1,
      natCode level, natCode_mem_stage_l hωTop level, ?_⟩
    have hAssignment :
        snoc (snoc (snoc ![A, B] Ordinal.omega0.toZFSet)
          (natCode 1)) (natCode level) =
          ![A, B, Ordinal.omega0.toZFSet, natCode 1, natCode level] := by
      funext position
      fin_cases position <;> rfl
    rw [hAssignment]
    exact (satisfiesIn_textbookEStageLevelAgreementCore_iff_l
      hTop hωTop hβtop hβ hωβ level hA hB hBValue).mpr hAgreement

end

end YesMetaZFC.BMS.ConstructibleBridge
