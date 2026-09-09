import BMSConstructibleBridge.TextbookAmbientTruthClassifierAbsolute
import BMSConstructibleBridge.TextbookEStageLevelAgreementFormula

/-!
# 具名层与当前层的 textbook E 真值一致性

固定有限 Levy 层后，本文件把具名集合 `A` 上的 textbook E 关系与当前
后继极限层中的有限真值轨迹分类器逐码比较。公式只使用成员语言；当前层不作为
参数出现，因而这正是 ambient 稳定公式所需的核心原子。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible
open Constructible.FiniteSequenceZF

set_option maxHeartbeats 800000

/--
九元布局为
`[A,omega,sigmaCode,levelCode,arity,code,E_A,A^arity,tuple]`。
-/
def textbookEAmbientAgreementBodyFor_l
    (classifier : FOFormula 5) : FOFormula 9 :=
  .conj
    (textbookEBoundedValueFormulaAt_l
      (0 : Fin 9) (4 : Fin 9) (5 : Fin 9) (6 : Fin 9))
    (.conj
      (Constructible.Model.finiteTupleSpaceFormulaAt
        (0 : Fin 9) (4 : Fin 9) (7 : Fin 9))
      (FOFormula.imp
        (.mem (8 : Fin 9) (7 : Fin 9))
        (FOFormula.biimp
          (.mem (8 : Fin 9) (6 : Fin 9))
          (FOFormula.rename ![1, 8, 2, 4, 5] classifier))))

/-- 六个公开参数上的单码 ambient 一致性公式。 -/
def textbookEAmbientAgreementFormulaFor_l
    (classifier : FOFormula 5) : FOFormula 6 :=
  externalExistentialClosure_l 2
    (FOFormula.all (textbookEAmbientAgreementBodyFor_l classifier))

/-- 单码公式精确比较具名集合的 E 关系与 ambient 分类器。 -/
theorem satisfiesIn_textbookEAmbientAgreementFormulaFor_natCode_iff_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top) (classifier : FOFormula 5)
    (positiveArity code level : Nat) {A : ZFSet.{u}}
    (hA : A ∈ LStageZF top) :
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        (textbookEAmbientAgreementFormulaFor_l classifier)
        ![A, Ordinal.omega0.toZFSet, natCode 1, natCode level,
          natCode positiveArity, natCode code] ↔
      ∀ tuple : ZFSet.{u}, tuple ∈ textbookTupleSpace A positiveArity →
        (tuple ∈ textbookEZF A (natCode positiveArity) (natCode code) ↔
          Model.SatisfiesIn (LStageZF top : Set ZFSet.{u}) classifier
            ![Ordinal.omega0.toZFSet, tuple, natCode 1,
              natCode positiveArity, natCode code]) := by
  rw [textbookEAmbientAgreementFormulaFor_l,
    satisfiesIn_externalExistentialClosure_l]
  change (∃ witnesses : Tuple ZFSet.{u} 2,
      (∀ position, witnesses position ∈ LStageZF top) ∧
      Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        (FOFormula.all (textbookEAmbientAgreementBodyFor_l classifier))
        (Fin.append
          ![A, Ordinal.omega0.toZFSet, natCode 1, natCode level,
            natCode positiveArity, natCode code] witnesses)) ↔ _
  constructor
  · rintro ⟨witnesses, hWitnesses, hAll⟩ tuple hTuple
    let relation := witnesses (0 : Fin 2)
    let tupleSpace := witnesses (1 : Fin 2)
    have hAppend :
        Fin.append
            ![A, Ordinal.omega0.toZFSet, natCode 1, natCode level,
              natCode positiveArity, natCode code] witnesses =
          ![A, Ordinal.omega0.toZFSet, natCode 1, natCode level,
            natCode positiveArity, natCode code, relation, tupleSpace] := by
      funext position
      fin_cases position <;> rfl
    rw [hAppend] at hAll
    have hTupleStage : tuple ∈ LStageZF top :=
      (LStageZF_isTransitive top).mem_trans hTuple
        (textbookTupleSpace_mem_LStageZF_l hTop hA positiveArity)
    have hBody := (satisfiesIn_all_stage_iff_l
      (LStageZF top : Set ZFSet.{u})
      (textbookEAmbientAgreementBodyFor_l classifier)
      ![A, Ordinal.omega0.toZFSet, natCode 1, natCode level,
        natCode positiveArity, natCode code, relation, tupleSpace]).mp
        hAll tuple hTupleStage
    have hSnoc :
        snoc
            ![A, Ordinal.omega0.toZFSet, natCode 1, natCode level,
              natCode positiveArity, natCode code, relation, tupleSpace]
            tuple =
          ![A, Ordinal.omega0.toZFSet, natCode 1, natCode level,
            natCode positiveArity, natCode code, relation, tupleSpace,
            tuple] := by
      funext position
      fin_cases position <;> rfl
    rw [hSnoc] at hBody
    simp only [textbookEAmbientAgreementBodyFor_l, Model.SatisfiesIn,
      Model.satisfiesIn_imp_iff, Model.satisfiesIn_biimp_iff,
      Model.satisfiesIn_rename] at hBody
    rcases hBody with ⟨hRelation, hSpace, hAgreement⟩
    have hFull : ∀ position : Fin 9,
        ![A, Ordinal.omega0.toZFSet, natCode 1, natCode level,
          natCode positiveArity, natCode code, relation, tupleSpace,
          tuple] position ∈ LStageZF top := by
      intro position
      fin_cases position
      · exact hA
      · exact omega_toZFSet_mem_stage_l hOmega
      · exact natCode_mem_stage_l hOmega 1
      · exact natCode_mem_stage_l hOmega level
      · exact natCode_mem_stage_l hOmega positiveArity
      · exact natCode_mem_stage_l hOmega code
      · exact hWitnesses 0
      · exact hWitnesses 1
      · exact hTupleStage
    have hRelationValue :=
      (satisfiesIn_textbookEBoundedValueFormulaAt_natCode_iff_l
        hTop hOmega (0 : Fin 9) (4 : Fin 9) (5 : Fin 9) (6 : Fin 9)
        ![A, Ordinal.omega0.toZFSet, natCode 1, natCode level,
          natCode positiveArity, natCode code, relation, tupleSpace,
          tuple] hFull positiveArity code rfl rfl).mp hRelation
    have hSpaceAssignment :
        (fun position =>
          ![A, Ordinal.omega0.toZFSet, natCode 1, natCode level,
            natCode positiveArity, natCode code, relation, tupleSpace,
            tuple]
            (![(0 : Fin 9), (4 : Fin 9), (7 : Fin 9)] position)) =
          ![A, natCode positiveArity, tupleSpace] := by
      funext position
      fin_cases position <;> rfl
    rw [Constructible.Model.finiteTupleSpaceFormulaAt,
      Model.satisfiesIn_rename, hSpaceAssignment] at hSpace
    have hSpaceValue :=
      (satisfiesIn_finiteTupleSpaceFormula_stage_natCode_iff_l
        hTop hOmega positiveArity hA (hWitnesses 1)).mp hSpace
    have hClassifierAssignment :
        (fun position =>
          ![A, Ordinal.omega0.toZFSet, natCode 1, natCode level,
            natCode positiveArity, natCode code, relation, tupleSpace,
            tuple] (![(1 : Fin 9), 8, 2, 4, 5] position)) =
          ![Ordinal.omega0.toZFSet, tuple, natCode 1,
            natCode positiveArity, natCode code] := by
      funext position
      fin_cases position <;> rfl
    rw [hClassifierAssignment] at hAgreement
    change tuple ∈ tupleSpace →
      (tuple ∈ relation ↔
        Model.SatisfiesIn (LStageZF top : Set ZFSet.{u}) classifier
          ![Ordinal.omega0.toZFSet, tuple, natCode 1,
            natCode positiveArity, natCode code]) at hAgreement
    change relation = textbookEZF A (natCode positiveArity)
      (natCode code) at hRelationValue
    change tupleSpace = textbookTupleSpace A positiveArity at hSpaceValue
    rw [hRelationValue] at hAgreement
    exact hAgreement (by simpa only [hSpaceValue] using hTuple)
  · intro hAgreement
    let relation := textbookEZF A (natCode positiveArity) (natCode code)
    let tupleSpace := textbookTupleSpace A positiveArity
    have hRelationStage : relation ∈ LStageZF top :=
      textbookEZF_mem_LStageZF_l hTop hA positiveArity code
    have hSpaceStage : tupleSpace ∈ LStageZF top :=
      textbookTupleSpace_mem_LStageZF_l hTop hA positiveArity
    refine ⟨![relation, tupleSpace], ?_, ?_⟩
    · intro position
      fin_cases position
      · exact hRelationStage
      · exact hSpaceStage
    · have hAppend :
          Fin.append
              ![A, Ordinal.omega0.toZFSet, natCode 1, natCode level,
                natCode positiveArity, natCode code]
              ![relation, tupleSpace] =
            ![A, Ordinal.omega0.toZFSet, natCode 1, natCode level,
              natCode positiveArity, natCode code, relation, tupleSpace] := by
        funext position
        fin_cases position <;> rfl
      rw [hAppend]
      apply (satisfiesIn_all_stage_iff_l
        (LStageZF top : Set ZFSet.{u})
        (textbookEAmbientAgreementBodyFor_l classifier)
        ![A, Ordinal.omega0.toZFSet, natCode 1, natCode level,
          natCode positiveArity, natCode code, relation, tupleSpace]).mpr
      intro tuple hTupleStage
      have hSnoc :
          snoc
              ![A, Ordinal.omega0.toZFSet, natCode 1, natCode level,
                natCode positiveArity, natCode code, relation, tupleSpace]
              tuple =
            ![A, Ordinal.omega0.toZFSet, natCode 1, natCode level,
              natCode positiveArity, natCode code, relation, tupleSpace,
              tuple] := by
        funext position
        fin_cases position <;> rfl
      rw [hSnoc]
      simp only [textbookEAmbientAgreementBodyFor_l, Model.SatisfiesIn,
        Model.satisfiesIn_imp_iff, Model.satisfiesIn_biimp_iff,
        Model.satisfiesIn_rename]
      have hFull : ∀ position : Fin 9,
          ![A, Ordinal.omega0.toZFSet, natCode 1, natCode level,
            natCode positiveArity, natCode code, relation, tupleSpace,
            tuple] position ∈ LStageZF top := by
        intro position
        fin_cases position
        · exact hA
        · exact omega_toZFSet_mem_stage_l hOmega
        · exact natCode_mem_stage_l hOmega 1
        · exact natCode_mem_stage_l hOmega level
        · exact natCode_mem_stage_l hOmega positiveArity
        · exact natCode_mem_stage_l hOmega code
        · exact hRelationStage
        · exact hSpaceStage
        · exact hTupleStage
      refine ⟨?_, ?_, ?_⟩
      · exact (satisfiesIn_textbookEBoundedValueFormulaAt_natCode_iff_l
          hTop hOmega (0 : Fin 9) (4 : Fin 9) (5 : Fin 9) (6 : Fin 9)
          ![A, Ordinal.omega0.toZFSet, natCode 1, natCode level,
            natCode positiveArity, natCode code, relation, tupleSpace,
            tuple] hFull positiveArity code rfl rfl).mpr rfl
      · rw [Constructible.Model.finiteTupleSpaceFormulaAt,
          Model.satisfiesIn_rename]
        have hSpaceAssignment :
            (fun position =>
              ![A, Ordinal.omega0.toZFSet, natCode 1, natCode level,
                natCode positiveArity, natCode code, relation, tupleSpace,
                tuple]
                (![(0 : Fin 9), (4 : Fin 9), (7 : Fin 9)] position)) =
              ![A, natCode positiveArity, tupleSpace] := by
          funext position
          fin_cases position <;> rfl
        rw [hSpaceAssignment]
        exact (satisfiesIn_finiteTupleSpaceFormula_stage_natCode_iff_l
          hTop hOmega positiveArity hA hSpaceStage).mpr rfl
      · change tuple ∈ tupleSpace →
          (tuple ∈ relation ↔
            Model.SatisfiesIn (LStageZF top : Set ZFSet.{u}) classifier
              ((fun position =>
                ![A, Ordinal.omega0.toZFSet, natCode 1, natCode level,
                  natCode positiveArity, natCode code, relation, tupleSpace,
                  tuple] (![(1 : Fin 9), 8, 2, 4, 5] position))))
        have hClassifierAssignment :
            (fun position =>
              ![A, Ordinal.omega0.toZFSet, natCode 1, natCode level,
                natCode positiveArity, natCode code, relation, tupleSpace,
                tuple] (![(1 : Fin 9), 8, 2, 4, 5] position)) =
              ![Ordinal.omega0.toZFSet, tuple, natCode 1,
                natCode positiveArity, natCode code] := by
          funext position
          fin_cases position <;> rfl
        rw [hClassifierAssignment]
        intro hTuple
        simpa only [relation, tupleSpace] using
          hAgreement tuple hTuple

/-! ## 统一有限层公式码 -/

/-- 具名集合与 ambient 层在全部正元 `Sigma_level` 码上的真值一致性。 -/
def TextbookEAmbientLevelAgreementFor_l (top : Ordinal.{u})
    (level : Nat) (A : ZFSet.{u}) (classifier : FOFormula 5) : Prop :=
  ∀ positiveArity code,
    TextbookBoundedIsSigmaCode_l level (positiveArity + 1) code →
      ∀ tuple : ZFSet.{u},
        tuple ∈ textbookTupleSpace A (positiveArity + 1) →
          (tuple ∈ textbookEZF A (natCode (positiveArity + 1))
              (natCode code) ↔
            Model.SatisfiesIn (LStageZF top : Set ZFSet.{u}) classifier
              ![Ordinal.omega0.toZFSet, tuple, natCode 1,
                natCode (positiveArity + 1), natCode code])

/--
六元布局为 `[A,omega,sigmaCode,levelCode,arity,code]`；前件先确认两个
自然数码、正元性和 `Sigma_level` 分类，再调用单码一致性公式。
-/
def textbookEAmbientLevelAgreementBodyFor_l
    (classifier : FOFormula 5) : FOFormula 6 :=
  FOFormula.imp
    (.mem (4 : Fin 6) (1 : Fin 6)) <|
  FOFormula.imp
    (.mem (5 : Fin 6) (1 : Fin 6)) <|
  FOFormula.imp
    (FOFormula.ex (.mem (6 : Fin 7) (4 : Fin 7))) <|
  FOFormula.imp
    boundedTextbookBoundedLevyClassifierDelta_l.toFO
    (textbookEAmbientAgreementFormulaFor_l classifier)

/-- 固定辅助常量后，对全部标准元数与公式码作比较。 -/
def textbookEAmbientLevelAgreementCoreFor_l
    (level : Nat) (classifier : FOFormula 5) : FOFormula 4 :=
  .conj
    (Constructible.Model.omegaSetAt (1 : Fin 4))
    (.conj
      (Delta0Formula.natLiteralDeltaAt 1 (2 : Fin 4)).toFO
      (.conj
        (Delta0Formula.natLiteralDeltaAt level (3 : Fin 4)).toFO
        (FOFormula.all <| FOFormula.all
          (textbookEAmbientLevelAgreementBodyFor_l classifier))))

/-- 一个公开集合参数上的统一 ambient 真值一致性公式。 -/
def textbookEAmbientLevelAgreementFormulaFor_l
    (level : Nat) (classifier : FOFormula 5) : FOFormula 1 :=
  externalExistentialClosure_l 3
    (textbookEAmbientLevelAgreementCoreFor_l level classifier)

/-- 有界分类器在具名真实层参数上精确识别标准 `Sigma_level` 公式码。 -/
theorem satisfiesIn_textbookEAmbientLevelClassifier_iff_l
    {top α : Ordinal.{u}} (hαtop : α < top)
    (hα : Order.IsSuccLimit α) (hOmegaα : Ordinal.omega0 < α)
    (level arity code : Nat) {A : ZFSet.{u}}
    (hA : A ∈ LStageZF top) (hAValue : A = LStageZF α) :
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        boundedTextbookBoundedLevyClassifierDelta_l.toFO
        ![A, Ordinal.omega0.toZFSet, natCode 1,
          natCode level, natCode arity, natCode code] ↔
      TextbookBoundedIsSigmaCode_l level arity code := by
  have hAssignment :
      ![A, Ordinal.omega0.toZFSet, natCode 1,
        natCode level, natCode arity, natCode code] =
        tupleCons (LStageZF α)
          (Delta0Formula.val
            (textbookBoundedLevyClassifierStageAssignment_l α hOmegaα
              (textbookSigmaJudgment_l level arity code))) := by
    rw [textbookBoundedLevyClassifierStageAssignment_value_l]
    funext position
    fin_cases position
    · exact hAValue
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  rw [hAssignment]
  exact (satisfiesIn_boundedTextbookBoundedLevyClassifier_iff_l
    hαtop hα hOmegaα (textbookSigmaJudgment_l level arity code)).trans
      (by simp [textbookSigmaJudgment_l,
        TextbookBoundedLevyJudgment.Certified])

/-- 规范辅助常量下的核心公式精确表达统一 ambient 真值一致性。 -/
theorem satisfiesIn_textbookEAmbientLevelAgreementCoreFor_iff_l
    {top α : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmegaTop : Ordinal.omega0 < top) (hαtop : α < top)
    (hα : Order.IsSuccLimit α) (hOmegaα : Ordinal.omega0 < α)
    (level : Nat) (classifier : FOFormula 5) {A : ZFSet.{u}}
    (hA : A ∈ LStageZF top) (hAValue : A = LStageZF α) :
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        (textbookEAmbientLevelAgreementCoreFor_l level classifier)
        ![A, Ordinal.omega0.toZFSet, natCode 1, natCode level] ↔
      TextbookEAmbientLevelAgreementFor_l top level A classifier := by
  let fixedAssignment : Tuple ZFSet.{u} 4 :=
    ![A, Ordinal.omega0.toZFSet, natCode 1, natCode level]
  have hFixedAssignment : ∀ position,
      fixedAssignment position ∈ LStageZF top := by
    intro position
    fin_cases position
    · exact hA
    · exact omega_toZFSet_mem_stage_l hOmegaTop
    · exact natCode_mem_stage_l hOmegaTop 1
    · exact natCode_mem_stage_l hOmegaTop level
  change Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
      (textbookEAmbientLevelAgreementCoreFor_l level classifier)
      fixedAssignment ↔ _
  simp only [textbookEAmbientLevelAgreementCoreFor_l,
    Model.SatisfiesIn]
  rw [Constructible.Model.satisfiesIn_omegaSetAt_iff hTop hOmegaTop
      (1 : Fin 4) fixedAssignment hFixedAssignment,
    satisfiesIn_natLiteralDeltaAt_stage_iff_l 1 (2 : Fin 4)
      fixedAssignment hFixedAssignment,
    satisfiesIn_natLiteralDeltaAt_stage_iff_l level (3 : Fin 4)
      fixedAssignment hFixedAssignment,
    satisfiesIn_all_stage_iff_l]
  dsimp [fixedAssignment]
  simp only [true_and]
  constructor
  · intro hAll positiveArity code hCode tuple hTuple
    let arity := positiveArity + 1
    have hArityStage : natCode arity ∈ LStageZF top :=
      natCode_mem_stage_l hOmegaTop arity
    have hCodeStage : natCode code ∈ LStageZF top :=
      natCode_mem_stage_l hOmegaTop code
    have hInner := hAll (natCode arity) hArityStage
    have hBody := (satisfiesIn_all_stage_iff_l
      (LStageZF top : Set ZFSet.{u})
      (textbookEAmbientLevelAgreementBodyFor_l classifier)
      (snoc ![A, Ordinal.omega0.toZFSet, natCode 1, natCode level]
        (natCode arity))).mp hInner (natCode code) hCodeStage
    have hSnoc :
        snoc (snoc
          ![A, Ordinal.omega0.toZFSet, natCode 1, natCode level]
          (natCode arity)) (natCode code) =
        ![A, Ordinal.omega0.toZFSet, natCode 1, natCode level,
          natCode arity, natCode code] := by
      funext position
      fin_cases position <;> rfl
    rw [hSnoc] at hBody
    simp only [textbookEAmbientLevelAgreementBodyFor_l,
      Model.satisfiesIn_imp_iff] at hBody
    have hArityOmega : natCode arity ∈ Ordinal.omega0.toZFSet :=
      (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode arity)).mpr ⟨arity, rfl⟩
    have hCodeOmega : natCode code ∈ Ordinal.omega0.toZFSet :=
      (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode code)).mpr ⟨code, rfl⟩
    have hPositive : ∃ member : ZFSet.{u},
        member ∈ LStageZF top ∧ member ∈ natCode arity :=
      ⟨natCode 0, natCode_mem_stage_l hOmegaTop 0,
        (IndexedSequenceZF.mem_natCode_iff_exists_lt
          (natCode 0) arity).mpr
            ⟨0, Nat.zero_lt_succ positiveArity, rfl⟩⟩
    have hClassifier :=
      (satisfiesIn_textbookEAmbientLevelClassifier_iff_l
        hαtop hα hOmegaα level arity code hA hAValue).mpr hCode
    have hAgreement := hBody hArityOmega hCodeOmega hPositive hClassifier
    exact (satisfiesIn_textbookEAmbientAgreementFormulaFor_natCode_iff_l
      hTop hOmegaTop classifier arity code level hA).mp hAgreement tuple hTuple
  · intro hAgreement arityValue hArityStage
    apply (satisfiesIn_all_stage_iff_l
      (LStageZF top : Set ZFSet.{u})
      (textbookEAmbientLevelAgreementBodyFor_l classifier)
      (snoc ![A, Ordinal.omega0.toZFSet, natCode 1, natCode level]
        arityValue)).mpr
    intro codeValue hCodeStage
    have hSnoc :
        snoc (snoc
          ![A, Ordinal.omega0.toZFSet, natCode 1, natCode level]
          arityValue) codeValue =
        ![A, Ordinal.omega0.toZFSet, natCode 1, natCode level,
          arityValue, codeValue] := by
      funext position
      fin_cases position <;> rfl
    rw [hSnoc]
    simp only [textbookEAmbientLevelAgreementBodyFor_l,
      Model.satisfiesIn_imp_iff]
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
          apply (satisfiesIn_textbookEAmbientLevelClassifier_iff_l
            hαtop hα hOmegaα level (positiveArity + 1) code
              hA hAValue).mp
          simpa only [Nat.succ_eq_add_one] using hClassifier
        apply (satisfiesIn_textbookEAmbientAgreementFormulaFor_natCode_iff_l
          hTop hOmegaTop classifier (positiveArity + 1) code level hA).mpr
        intro tuple hTuple
        exact hAgreement positiveArity code hCertified tuple hTuple

/-- 公开一元公式精确表达具名层与 ambient 层的统一真值一致性。 -/
theorem satisfiesIn_textbookEAmbientLevelAgreementFormulaFor_iff_l
    {top α : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmegaTop : Ordinal.omega0 < top) (hαtop : α < top)
    (hα : Order.IsSuccLimit α) (hOmegaα : Ordinal.omega0 < α)
    (level : Nat) (classifier : FOFormula 5) {A : ZFSet.{u}}
    (hA : A ∈ LStageZF top) (hAValue : A = LStageZF α) :
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        (textbookEAmbientLevelAgreementFormulaFor_l level classifier) ![A] ↔
      TextbookEAmbientLevelAgreementFor_l top level A classifier := by
  rw [textbookEAmbientLevelAgreementFormulaFor_l,
    satisfiesIn_externalExistentialClosure_l]
  change (∃ witnesses : Tuple ZFSet.{u} 3,
      (∀ position, witnesses position ∈ LStageZF top) ∧
      Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        (textbookEAmbientLevelAgreementCoreFor_l level classifier)
        (Fin.append ![A] witnesses)) ↔ _
  constructor
  · rintro ⟨witnesses, hWitnesses, hCore⟩
    let omegaValue := witnesses (0 : Fin 3)
    let sigmaValue := witnesses (1 : Fin 3)
    let levelValue := witnesses (2 : Fin 3)
    have hAppend : Fin.append ![A] witnesses =
        ![A, omegaValue, sigmaValue, levelValue] := by
      funext position
      fin_cases position <;> rfl
    rw [hAppend] at hCore
    have hFull : ∀ position : Fin 4,
        ![A, omegaValue, sigmaValue, levelValue] position ∈
          LStageZF top := by
      intro position
      fin_cases position
      · exact hA
      · exact hWitnesses 0
      · exact hWitnesses 1
      · exact hWitnesses 2
    have hParts := hCore
    simp only [textbookEAmbientLevelAgreementCoreFor_l,
      Model.SatisfiesIn] at hParts
    rcases hParts with ⟨hOmegaFormula, hSigmaFormula,
      hLevelFormula, hRest⟩
    have hOmegaValue : omegaValue = Ordinal.omega0.toZFSet :=
      (Constructible.Model.satisfiesIn_omegaSetAt_iff
        hTop hOmegaTop (1 : Fin 4)
        ![A, omegaValue, sigmaValue, levelValue] hFull).mp hOmegaFormula
    have hSigmaValue : sigmaValue = natCode 1 :=
      (satisfiesIn_natLiteralDeltaAt_stage_iff_l
        1 (2 : Fin 4) ![A, omegaValue, sigmaValue, levelValue]
        hFull).mp hSigmaFormula
    have hLevelValue : levelValue = natCode level :=
      (satisfiesIn_natLiteralDeltaAt_stage_iff_l
        level (3 : Fin 4) ![A, omegaValue, sigmaValue, levelValue]
        hFull).mp hLevelFormula
    have hCanonical : ![A, omegaValue, sigmaValue, levelValue] =
        ![A, Ordinal.omega0.toZFSet, natCode 1, natCode level] := by
      funext position
      fin_cases position
      · rfl
      · exact hOmegaValue
      · exact hSigmaValue
      · exact hLevelValue
    rw [hCanonical] at hOmegaFormula hSigmaFormula hLevelFormula hRest
    apply (satisfiesIn_textbookEAmbientLevelAgreementCoreFor_iff_l
      hTop hOmegaTop hαtop hα hOmegaα level classifier hA hAValue).mp
    simpa only [textbookEAmbientLevelAgreementCoreFor_l,
      Model.SatisfiesIn] using
      (show Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        (textbookEAmbientLevelAgreementCoreFor_l level classifier)
        ![A, Ordinal.omega0.toZFSet, natCode 1, natCode level] from
          ⟨hOmegaFormula, hSigmaFormula, hLevelFormula, hRest⟩)
  · intro hAgreement
    refine ⟨![Ordinal.omega0.toZFSet, natCode 1, natCode level], ?_, ?_⟩
    · intro position
      fin_cases position
      · exact omega_toZFSet_mem_stage_l hOmegaTop
      · exact natCode_mem_stage_l hOmegaTop 1
      · exact natCode_mem_stage_l hOmegaTop level
    · have hAppend :
          Fin.append ![A]
              ![Ordinal.omega0.toZFSet, natCode 1, natCode level] =
            ![A, Ordinal.omega0.toZFSet, natCode 1, natCode level] := by
        funext position
        fin_cases position <;> rfl
      rw [hAppend]
      exact (satisfiesIn_textbookEAmbientLevelAgreementCoreFor_iff_l
        hTop hOmegaTop hαtop hα hOmegaα level classifier hA hAValue).mpr
          hAgreement

end YesMetaZFC.BMS.ConstructibleBridge
