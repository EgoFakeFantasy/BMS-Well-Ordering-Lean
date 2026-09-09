import BMSConstructibleBridge.TextbookBoundedLevyClassifierBounded
import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEUniformWitnessFormula

/-!
# 两个集合大小结构上的 textbook E 真值一致性

本模块先构造稳定关系中最核心的语义原子：对于一个正元公式码，两个集合
`A`、`B` 上的 textbook `E` 满足关系在所有 `A`-赋值上一致。公式本身不引用
Lean 的 `FOFormula.Satisfies`；它只量化三个集合输出（两份 `E` 关系和有限元组
空间），再对元组空间作有界语义比较。

这里先给出整个可构造宇宙 `L` 中的精确语义。后续文件将同一原子放入已命名
阶段并利用相对化，把它降为原生 `Delta0`。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible
open Constructible.FiniteSequenceZF

/-!
公开布局为 `[A,B,positiveArity,code]`。三个存在见证依次为 `E_A`、`E_B`、
`A^positiveArity`，最后一个全称变量是待比较的元组图。
-/

/-- 八元核心同时核验两份 `E` 输出、元组空间和一个元组的真值一致性。 -/
def textbookEAgreementBody_l : FOFormula 8 :=
  .conj
    (Constructible.Model.textbookEZFFormulaAt
      (0 : Fin 8) (2 : Fin 8) (3 : Fin 8) (4 : Fin 8))
    (.conj
      (Constructible.Model.textbookEZFFormulaAt
        (1 : Fin 8) (2 : Fin 8) (3 : Fin 8) (5 : Fin 8))
      (.conj
        (Constructible.Model.finiteTupleSpaceFormulaAt
          (0 : Fin 8) (2 : Fin 8) (6 : Fin 8))
        (FOFormula.imp
          (.mem (7 : Fin 8) (6 : Fin 8))
          (FOFormula.biimp
            (.mem (7 : Fin 8) (4 : Fin 8))
            (.mem (7 : Fin 8) (5 : Fin 8))))))

/-- 四个公开参数上的一致性公式。 -/
def textbookEAgreementFormula_l : FOFormula 4 :=
  .ex <| .ex <| .ex <| FOFormula.all textbookEAgreementBody_l

/--
在标准自然数码处，一致性公式恰好比较两个 textbook `E` 关系在所有
`A^n` 元组上的成员资格。
-/
theorem satisfies_textbookEAgreementFormula_natCode_iff_l
    (A B : Constructible.Model.LCarrier.{u}) (positiveArity code : Nat) :
    FOFormula.Satisfies Constructible.Model.lCarrierMem
        textbookEAgreementFormula_l
        ![A, B,
          Constructible.TextbookNatFormula.textbookNatCodeLCarrier
            positiveArity,
          Constructible.TextbookNatFormula.textbookNatCodeLCarrier code] ↔
      ∀ tuple : Constructible.Model.LCarrier.{u},
        tuple.1 ∈ textbookTupleSpace A.1 positiveArity →
          (tuple.1 ∈ textbookEZF A.1 (natCode positiveArity) (natCode code) ↔
            tuple.1 ∈ textbookEZF B.1 (natCode positiveArity)
              (natCode code)) := by
  simp only [textbookEAgreementFormula_l, FOFormula.Satisfies,
    FOFormula.satisfies_all]
  constructor
  · rintro ⟨leftRelation, rightRelation, tupleSpace, hBody⟩ tuple hTuple
    have hAt := hBody tuple
    have hAssignment :
        snoc (snoc (snoc (snoc
          ![A, B,
            Constructible.TextbookNatFormula.textbookNatCodeLCarrier
              positiveArity,
            Constructible.TextbookNatFormula.textbookNatCodeLCarrier code]
          leftRelation) rightRelation) tupleSpace) tuple =
        ![A, B,
          Constructible.TextbookNatFormula.textbookNatCodeLCarrier
            positiveArity,
          Constructible.TextbookNatFormula.textbookNatCodeLCarrier code,
          leftRelation, rightRelation, tupleSpace, tuple] := by
      funext position
      fin_cases position <;> rfl
    rw [hAssignment] at hAt
    simp only [textbookEAgreementBody_l, FOFormula.Satisfies,
      Constructible.Model.satisfies_textbookEZFFormulaAt_lCarrier,
      Constructible.Model.satisfies_finiteTupleSpaceFormulaAt_lCarrier,
      FOFormula.satisfies_imp, FOFormula.satisfies_biimp] at hAt
    rcases hAt with ⟨hLeft, hRight, hSpace, hAgreement⟩
    change
      ((Constructible.TextbookNatFormula.textbookNatCodeLCarrier
          positiveArity).1 ∈ textbookEOmegaZF ∧
        (Constructible.TextbookNatFormula.textbookNatCodeLCarrier code).1 ∈
          textbookEOmegaZF) ∧
        leftRelation.1 = textbookEZF A.1
          (Constructible.TextbookNatFormula.textbookNatCodeLCarrier
            positiveArity).1
          (Constructible.TextbookNatFormula.textbookNatCodeLCarrier code).1
        at hLeft
    change
      ((Constructible.TextbookNatFormula.textbookNatCodeLCarrier
          positiveArity).1 ∈ textbookEOmegaZF ∧
        (Constructible.TextbookNatFormula.textbookNatCodeLCarrier code).1 ∈
          textbookEOmegaZF) ∧
        rightRelation.1 = textbookEZF B.1
          (Constructible.TextbookNatFormula.textbookNatCodeLCarrier
            positiveArity).1
          (Constructible.TextbookNatFormula.textbookNatCodeLCarrier code).1
        at hRight
    change FOFormula.Satisfies Constructible.Model.lCarrierMem
      Constructible.ContinuumFormula.finiteTupleSpaceFormula
      ![A,
        Constructible.TextbookNatFormula.textbookNatCodeLCarrier
          positiveArity,
        tupleSpace] at hSpace
    change tuple.1 ∈ tupleSpace.1 →
      (tuple.1 ∈ leftRelation.1 ↔ tuple.1 ∈ rightRelation.1) at hAgreement
    have hLeftValue := hLeft.2
    have hRightValue := hRight.2
    have hSpaceValue :=
      (Constructible.ContinuumFormula.satisfies_finiteTupleSpaceFormula_natCode_iff
        A tupleSpace positiveArity).mp (by
          simpa using hSpace)
    have hCompared := hAgreement (by simpa only [hSpaceValue] using hTuple)
    simpa only [hLeftValue, hRightValue,
      Constructible.TextbookNatFormula.textbookNatCodeLCarrier_val] using
      hCompared
  · intro hAgreement
    let leftRelation : Constructible.Model.LCarrier.{u} :=
      Constructible.Model.textbookEZFLCarrier A positiveArity code
    let rightRelation : Constructible.Model.LCarrier.{u} :=
      Constructible.Model.textbookEZFLCarrier B positiveArity code
    let tupleSpace : Constructible.Model.LCarrier.{u} :=
      Constructible.ContinuumFormula.finiteTupleSpaceLCarrier A positiveArity
    refine ⟨leftRelation, rightRelation, tupleSpace, ?_⟩
    intro tuple
    have hAssignment :
        snoc (snoc (snoc (snoc
          ![A, B,
            Constructible.TextbookNatFormula.textbookNatCodeLCarrier
              positiveArity,
            Constructible.TextbookNatFormula.textbookNatCodeLCarrier code]
          leftRelation) rightRelation) tupleSpace) tuple =
        ![A, B,
          Constructible.TextbookNatFormula.textbookNatCodeLCarrier
            positiveArity,
          Constructible.TextbookNatFormula.textbookNatCodeLCarrier code,
          leftRelation, rightRelation, tupleSpace, tuple] := by
      funext position
      fin_cases position <;> rfl
    rw [hAssignment]
    simp only [textbookEAgreementBody_l, FOFormula.Satisfies,
      Constructible.Model.satisfies_textbookEZFFormulaAt_lCarrier,
      Constructible.Model.satisfies_finiteTupleSpaceFormulaAt_lCarrier,
      FOFormula.satisfies_imp, FOFormula.satisfies_biimp]
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine ⟨?_, rfl⟩
      constructor
      · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
          (natCode positiveArity)).mpr ⟨positiveArity, rfl⟩
      · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
          (natCode code)).mpr ⟨code, rfl⟩
    · refine ⟨?_, rfl⟩
      constructor
      · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
          (natCode positiveArity)).mpr ⟨positiveArity, rfl⟩
      · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
          (natCode code)).mpr ⟨code, rfl⟩
    · exact
        (Constructible.ContinuumFormula.satisfies_finiteTupleSpaceFormula_natCode_iff
          A tupleSpace positiveArity).mpr rfl
    · change tuple.1 ∈ tupleSpace.1 →
        (tuple.1 ∈ leftRelation.1 ↔ tuple.1 ∈ rightRelation.1)
      intro hTuple
      simpa only [leftRelation, rightRelation,
        Constructible.Model.textbookEZFLCarrier_val,
        Constructible.TextbookNatFormula.textbookNatCodeLCarrier_val] using
        hAgreement tuple (by
          simpa only [tupleSpace,
            Constructible.ContinuumFormula.finiteTupleSpaceLCarrier_val] using
            hTuple)

/-! ## 统一有限层公式码 -/

/-- 两个构造集合在给定有限 `Sigma` 层的全部 textbook E 真值上一致。 -/
def TextbookELevelAgreement_l (level : Nat)
    (A B : Constructible.Model.LCarrier.{u}) : Prop :=
  ∀ positiveArity code,
    TextbookBoundedIsSigmaCode_l level (positiveArity + 1) code →
      ∀ tuple : Constructible.Model.LCarrier.{u},
        tuple.1 ∈ textbookTupleSpace A.1 (positiveArity + 1) →
          (tuple.1 ∈ textbookEZF A.1 (natCode (positiveArity + 1))
              (natCode code) ↔
            tuple.1 ∈ textbookEZF B.1 (natCode (positiveArity + 1))
              (natCode code))

/-!
七元布局为 `[A,B,omega,sigmaCode,levelCode,arity,code]`。最后两个坐标由
两个全称量词引入；前三个辅助常量随后在公开公式中存在量化。
-/

/-- 统一层级比较的七元量词体。 -/
def textbookELevelAgreementBody_l : FOFormula 7 :=
  FOFormula.imp
    (.conj
      (.mem (5 : Fin 7) (2 : Fin 7))
      (.conj
        (.mem (6 : Fin 7) (2 : Fin 7))
        (.conj
          (FOFormula.ex (.mem (7 : Fin 8) (5 : Fin 8)))
          (FOFormula.rename ![1, 2, 3, 4, 5, 6]
            boundedTextbookBoundedLevyClassifierDelta_l.toFO))))
    (FOFormula.rename ![0, 1, 5, 6] textbookEAgreementFormula_l)

/-- 固定三个辅助常量后，对全部自然数元数和公式码作比较。 -/
def textbookELevelAgreementCore_l (level : Nat) : FOFormula 5 :=
  .conj
    (Constructible.Model.omegaSetAt (2 : Fin 5))
    (.conj
      (Delta0Formula.natLiteralDeltaAt 1 (3 : Fin 5)).toFO
      (.conj
        (Delta0Formula.natLiteralDeltaAt level (4 : Fin 5)).toFO
        (FOFormula.all <| FOFormula.all textbookELevelAgreementBody_l)))

/-- 只有两个公开集合参数的统一有限层 textbook E 一致性公式。 -/
def textbookELevelAgreementFormula_l (level : Nat) : FOFormula 2 :=
  .ex <| .ex <| .ex <| textbookELevelAgreementCore_l level

/-- 把有限 `Sigma` 层级、元数和公式码组成分类判断。 -/
def textbookSigmaJudgment_l (level arity code : Nat) :
    TextbookBoundedLevyJudgment :=
  { isSigma := true, level := level, arity := arity, code := code }

/-- 层级比较体中分类器的六个坐标恰是有界分类器的规范赋值。 -/
theorem textbookELevelClassifierAssignment_value_l
    (level arity code : Nat) (A B : Constructible.Model.LCarrier.{u})
    (β : Ordinal.{u}) (hB : B.1 = LStageZF β)
    (hω : Ordinal.omega0 < β) :
    (fun i =>
      (![A, B, Constructible.Model.omegaLCarrier,
        Constructible.TextbookNatFormula.textbookNatCodeLCarrier 1,
        Constructible.TextbookNatFormula.textbookNatCodeLCarrier level,
        Constructible.TextbookNatFormula.textbookNatCodeLCarrier arity,
        Constructible.TextbookNatFormula.textbookNatCodeLCarrier code]
        (![1, 2, 3, 4, 5, 6] i)).1) =
      tupleCons (LStageZF β)
        (Delta0Formula.val
          (textbookBoundedLevyClassifierStageAssignment_l β hω
            (textbookSigmaJudgment_l level arity code))) := by
  funext position
  fin_cases position
  · exact hB
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- 七元层级比较赋值上的有界分类器精确识别 `Sigma_level` 公式码。 -/
theorem satisfies_textbookELevelClassifier_iff_l
    (level arity code : Nat) (A B : Constructible.Model.LCarrier.{u})
    (β : Ordinal.{u}) (hB : B.1 = LStageZF β)
    (hβ : Order.IsSuccLimit β) (hω : Ordinal.omega0 < β) :
    FOFormula.Satisfies Constructible.Model.lCarrierMem
        (FOFormula.rename ![1, 2, 3, 4, 5, 6]
          boundedTextbookBoundedLevyClassifierDelta_l.toFO)
        ![A, B, Constructible.Model.omegaLCarrier,
          Constructible.TextbookNatFormula.textbookNatCodeLCarrier 1,
          Constructible.TextbookNatFormula.textbookNatCodeLCarrier level,
          Constructible.TextbookNatFormula.textbookNatCodeLCarrier arity,
          Constructible.TextbookNatFormula.textbookNatCodeLCarrier code] ↔
      TextbookBoundedIsSigmaCode_l level arity code := by
  rw [FOFormula.satisfies_rename, Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_lCarrier_absolute,
    textbookELevelClassifierAssignment_value_l level arity code A B β hB hω,
    satisfies_boundedTextbookBoundedLevyClassifierDelta_iff_l hβ hω]
  simp [textbookSigmaJudgment_l, TextbookBoundedLevyJudgment.Certified]

/-- 固定规范辅助常量后，核心公式精确表达统一层级一致性。 -/
theorem satisfies_textbookELevelAgreementCore_iff_l
    (level : Nat) (A B : Constructible.Model.LCarrier.{u})
    (β : Ordinal.{u}) (hB : B.1 = LStageZF β)
    (hβ : Order.IsSuccLimit β) (hω : Ordinal.omega0 < β) :
    FOFormula.Satisfies Constructible.Model.lCarrierMem
        (textbookELevelAgreementCore_l level)
        ![A, B, Constructible.Model.omegaLCarrier,
          Constructible.TextbookNatFormula.textbookNatCodeLCarrier 1,
          Constructible.TextbookNatFormula.textbookNatCodeLCarrier level] ↔
      TextbookELevelAgreement_l level A B := by
  simp only [textbookELevelAgreementCore_l, FOFormula.Satisfies,
    Constructible.Model.satisfies_omegaSetAt,
    Constructible.TextbookNatFormula.satisfies_natLiteralDeltaAt_toFO_lCarrier,
    FOFormula.satisfies_all]
  constructor
  · rintro ⟨_hOmega, _hSigma, _hLevel, hAll⟩
    intro positiveArity code hCode tuple hTuple
    let arity := positiveArity + 1
    let arityValue : Constructible.Model.LCarrier.{u} :=
      Constructible.TextbookNatFormula.textbookNatCodeLCarrier arity
    let codeValue : Constructible.Model.LCarrier.{u} :=
      Constructible.TextbookNatFormula.textbookNatCodeLCarrier code
    have hBody := hAll arityValue codeValue
    have hAssignment :
        snoc (snoc
          ![A, B, Constructible.Model.omegaLCarrier,
            Constructible.TextbookNatFormula.textbookNatCodeLCarrier 1,
            Constructible.TextbookNatFormula.textbookNatCodeLCarrier level]
          arityValue) codeValue =
        ![A, B, Constructible.Model.omegaLCarrier,
          Constructible.TextbookNatFormula.textbookNatCodeLCarrier 1,
          Constructible.TextbookNatFormula.textbookNatCodeLCarrier level,
          arityValue, codeValue] := by
      funext position
      fin_cases position <;> rfl
    rw [hAssignment] at hBody
    simp only [textbookELevelAgreementBody_l,
      FOFormula.satisfies_imp, FOFormula.Satisfies,
      FOFormula.satisfies_rename] at hBody
    have hAgreementFormula :
        FOFormula.Satisfies Constructible.Model.lCarrierMem
          textbookEAgreementFormula_l
          ![A, B,
            Constructible.TextbookNatFormula.textbookNatCodeLCarrier arity,
            Constructible.TextbookNatFormula.textbookNatCodeLCarrier code] := by
      apply hBody
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
          (natCode arity)).mpr ⟨arity, rfl⟩
      · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
          (natCode code)).mpr ⟨code, rfl⟩
      · refine ⟨Constructible.TextbookNatFormula.textbookNatCodeLCarrier 0, ?_⟩
        exact (IndexedSequenceZF.mem_natCode_iff_exists_lt
          (natCode 0) arity).mpr
          ⟨0, Nat.zero_lt_succ positiveArity, rfl⟩
      · have hClassifier :=
          (satisfies_textbookELevelClassifier_iff_l
            level arity code A B β hB hβ hω).mpr hCode
        simpa only [FOFormula.satisfies_rename,
          Delta0Formula.satisfies_toFO] using hClassifier
    exact ((satisfies_textbookEAgreementFormula_natCode_iff_l
      A B arity code).mp hAgreementFormula) tuple hTuple
  · intro hAgreement
    refine ⟨rfl, rfl, rfl, ?_⟩
    intro arityValue codeValue
    have hAssignment :
        snoc (snoc
          ![A, B, Constructible.Model.omegaLCarrier,
            Constructible.TextbookNatFormula.textbookNatCodeLCarrier 1,
            Constructible.TextbookNatFormula.textbookNatCodeLCarrier level]
          arityValue) codeValue =
        ![A, B, Constructible.Model.omegaLCarrier,
          Constructible.TextbookNatFormula.textbookNatCodeLCarrier 1,
          Constructible.TextbookNatFormula.textbookNatCodeLCarrier level,
          arityValue, codeValue] := by
      funext position
      fin_cases position <;> rfl
    rw [hAssignment]
    simp only [textbookELevelAgreementBody_l,
      FOFormula.satisfies_imp, FOFormula.Satisfies,
      FOFormula.satisfies_rename]
    rintro ⟨hArityOmega, hCodeOmega, hArityPositive, hClassifier⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode
      arityValue.1).mp hArityOmega with ⟨arity, hArity⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode
      codeValue.1).mp hCodeOmega with ⟨code, hCode⟩
    have hArityValue : arityValue =
        Constructible.TextbookNatFormula.textbookNatCodeLCarrier arity :=
      Subtype.ext hArity
    have hCodeValue : codeValue =
        Constructible.TextbookNatFormula.textbookNatCodeLCarrier code :=
      Subtype.ext hCode
    subst arityValue
    subst codeValue
    cases arity with
    | zero =>
      rcases hArityPositive with ⟨member, hMember⟩
      exfalso
      change member.1 ∈
        (Constructible.TextbookNatFormula.textbookNatCodeLCarrier 0).1 at hMember
      simpa using hMember
    | succ positiveArity =>
      have hClassifierFormula :
        FOFormula.Satisfies Constructible.Model.lCarrierMem
          (FOFormula.rename ![1, 2, 3, 4, 5, 6]
            boundedTextbookBoundedLevyClassifierDelta_l.toFO)
          ![A, B, Constructible.Model.omegaLCarrier,
            Constructible.TextbookNatFormula.textbookNatCodeLCarrier 1,
            Constructible.TextbookNatFormula.textbookNatCodeLCarrier level,
            Constructible.TextbookNatFormula.textbookNatCodeLCarrier
              (positiveArity + 1),
            Constructible.TextbookNatFormula.textbookNatCodeLCarrier code] := by
        simpa only [FOFormula.satisfies_rename,
          Delta0Formula.satisfies_toFO, Nat.succ_eq_add_one] using hClassifier
      have hCodeCertified :
          TextbookBoundedIsSigmaCode_l level (positiveArity + 1) code := by
        simpa [Nat.succ_eq_add_one] using
          (satisfies_textbookELevelClassifier_iff_l
            level (positiveArity + 1) code A B β hB hβ hω).mp
              hClassifierFormula
      exact (satisfies_textbookEAgreementFormula_natCode_iff_l
        A B (positiveArity + 1) code).mpr
          (hAgreement positiveArity code hCodeCertified)

/-- 公开二元公式在 `L` 中精确表达统一有限层一致性。 -/
theorem satisfies_textbookELevelAgreementFormula_iff_l
    (level : Nat) (A B : Constructible.Model.LCarrier.{u})
    (β : Ordinal.{u}) (hB : B.1 = LStageZF β)
    (hβ : Order.IsSuccLimit β) (hω : Ordinal.omega0 < β) :
    FOFormula.Satisfies Constructible.Model.lCarrierMem
        (textbookELevelAgreementFormula_l level) ![A, B] ↔
      TextbookELevelAgreement_l level A B := by
  simp only [textbookELevelAgreementFormula_l, FOFormula.Satisfies]
  constructor
  · rintro ⟨omegaValue, sigmaValue, levelValue, hCore⟩
    have hAssignment :
        snoc (snoc (snoc ![A, B] omegaValue) sigmaValue) levelValue =
          ![A, B, omegaValue, sigmaValue, levelValue] := by
      funext position
      fin_cases position <;> rfl
    rw [hAssignment] at hCore
    simp only [textbookELevelAgreementCore_l, FOFormula.Satisfies,
      Constructible.Model.satisfies_omegaSetAt,
      Constructible.TextbookNatFormula.satisfies_natLiteralDeltaAt_toFO_lCarrier]
      at hCore
    rcases hCore with ⟨hOmega, hSigma, hLevel, hRest⟩
    have hOmegaValue : omegaValue = Constructible.Model.omegaLCarrier := hOmega
    have hSigmaValue : sigmaValue =
        Constructible.TextbookNatFormula.textbookNatCodeLCarrier 1 :=
      Subtype.ext hSigma
    have hLevelValue : levelValue =
        Constructible.TextbookNatFormula.textbookNatCodeLCarrier level :=
      Subtype.ext hLevel
    subst omegaValue
    subst sigmaValue
    subst levelValue
    apply (satisfies_textbookELevelAgreementCore_iff_l
      level A B β hB hβ hω).mp
    simp only [textbookELevelAgreementCore_l, FOFormula.Satisfies,
      Constructible.Model.satisfies_omegaSetAt,
      Constructible.TextbookNatFormula.satisfies_natLiteralDeltaAt_toFO_lCarrier]
    exact ⟨rfl, rfl, rfl, hRest⟩
  · intro hAgreement
    refine ⟨Constructible.Model.omegaLCarrier,
      Constructible.TextbookNatFormula.textbookNatCodeLCarrier 1,
      Constructible.TextbookNatFormula.textbookNatCodeLCarrier level, ?_⟩
    have hAssignment :
        snoc (snoc (snoc ![A, B] Constructible.Model.omegaLCarrier)
          (Constructible.TextbookNatFormula.textbookNatCodeLCarrier 1))
          (Constructible.TextbookNatFormula.textbookNatCodeLCarrier level) =
        ![A, B, Constructible.Model.omegaLCarrier,
          Constructible.TextbookNatFormula.textbookNatCodeLCarrier 1,
          Constructible.TextbookNatFormula.textbookNatCodeLCarrier level] := by
      funext position
      fin_cases position <;> rfl
    rw [hAssignment]
    exact (satisfies_textbookELevelAgreementCore_iff_l
      level A B β hB hβ hω).mpr
      hAgreement

end YesMetaZFC.BMS.ConstructibleBridge
