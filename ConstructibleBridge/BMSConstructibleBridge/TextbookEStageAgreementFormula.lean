import BMSConstructibleBridge.TextbookEBoundedFormula
import BMSConstructibleBridge.TextbookLevyClassifierBounded
import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEUniformWitnessFormula

/-!
# 后继极限层中的 textbook E 统一一致性公式

本模块以有限元数截断 E 公式替换只在整个 `L` 中有总性证明的旧公式，因而
统一一致性公式可以在任意严格越过 `omega` 的后继极限层内求值。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible
open Constructible.FiniteSequenceZF

noncomputable section

/-- 把层稳定 E 值公式放到任意四个坐标。 -/
def textbookEBoundedValueFormulaAt_l {n : Nat}
    (ambient positiveArity code output : Fin n) : FOFormula n :=
  FOFormula.rename ![ambient, positiveArity, code, output]
    TextbookEBoundedFormula_l.valueFormula

/-- 有限元组空间公式在后继极限层中精确计算标准有限幂。 -/
theorem satisfiesIn_finiteTupleSpaceFormula_stage_natCode_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (arity : Nat)
    {seed space : ZFSet.{u}} (hseed : seed ∈ LStageZF θ)
    (hspace : space ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        Constructible.ContinuumFormula.finiteTupleSpaceFormula
        ![seed, natCode arity, space] ↔
      space = textbookTupleSpace seed arity := by
  rw [Constructible.ContinuumFormula.finiteTupleSpaceFormula,
    Constructible.Model.satisfiesIn_rename]
  have hAssignment :
      (fun position => ![seed, natCode arity, space]
        (Constructible.ContinuumFormula.finiteTupleSpaceFormulaRename
          position)) =
        ![natCode arity, seed, space] := by
    funext position
    fin_cases position <;> rfl
  rw [hAssignment]
  simpa only [textbookTupleSpace] using
    satisfiesIn_finiteFunctionSpaceGraph_stage_natCode_iff_l
      hθ hω arity hseed hspace

/-- 八元核心比较两个参数集合上的 E 真值，并把全称量词限制到元组空间。 -/
def textbookEStageAgreementBody_l : FOFormula 8 :=
  .conj
    (textbookEBoundedValueFormulaAt_l
      (0 : Fin 8) (2 : Fin 8) (3 : Fin 8) (4 : Fin 8))
    (.conj
      (textbookEBoundedValueFormulaAt_l
        (1 : Fin 8) (2 : Fin 8) (3 : Fin 8) (5 : Fin 8))
      (.conj
        (Constructible.Model.finiteTupleSpaceFormulaAt
          (0 : Fin 8) (2 : Fin 8) (6 : Fin 8))
        (FOFormula.imp
          (.mem (7 : Fin 8) (6 : Fin 8))
          (FOFormula.biimp
            (.mem (7 : Fin 8) (4 : Fin 8))
            (.mem (7 : Fin 8) (5 : Fin 8))))))

/-- 布局 `[A,B,positiveArity,code]` 的层内 E 一致性公式。 -/
def textbookEStageAgreementFormula_l : FOFormula 4 :=
  .ex <| .ex <| .ex <| FOFormula.all textbookEStageAgreementBody_l

/-- 层内 E 值坐标公式在标准码处精确计算。 -/
theorem satisfiesIn_textbookEBoundedValueFormulaAt_natCode_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) {n : Nat}
    (ambient positiveArity code output : Fin n)
    (assignment : Tuple ZFSet.{u} n)
    (hAssignment : ∀ position, assignment position ∈ LStageZF θ)
    (arityCode formulaCode : Nat)
    (hArity : assignment positiveArity = natCode arityCode)
    (hCode : assignment code = natCode formulaCode) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        (textbookEBoundedValueFormulaAt_l
          ambient positiveArity code output) assignment ↔
      assignment output = Constructible.textbookEZF
        (assignment ambient) (natCode arityCode) (natCode formulaCode) := by
  rw [textbookEBoundedValueFormulaAt_l,
    Constructible.Model.satisfiesIn_rename]
  have hSelected :
      (fun position => assignment
        (![ambient, positiveArity, code, output] position)) =
        ![assignment ambient, natCode arityCode,
          natCode formulaCode, assignment output] := by
    funext position
    fin_cases position
    · rfl
    · exact hArity
    · exact hCode
    · rfl
  rw [hSelected]
  exact satisfiesIn_textbookEBoundedValueFormula_natCode_iff_l
    hθ hω arityCode formulaCode
      (hAssignment ambient) (hAssignment output)

/-- 在标准码处，层内一致性公式恰好比较所有参数元组上的 E 成员关系。 -/
theorem satisfiesIn_textbookEStageAgreementFormula_natCode_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (positiveArity code : Nat)
    {A B : ZFSet.{u}} (hA : A ∈ LStageZF θ) (hB : B ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookEStageAgreementFormula_l
        ![A, B, natCode positiveArity, natCode code] ↔
      ∀ tuple : ZFSet.{u}, tuple ∈ textbookTupleSpace A positiveArity →
        (tuple ∈ textbookEZF A (natCode positiveArity) (natCode code) ↔
          tuple ∈ textbookEZF B (natCode positiveArity) (natCode code)) := by
  simp only [textbookEStageAgreementFormula_l,
    Constructible.Model.SatisfiesIn, satisfiesIn_all_stage_iff_l]
  constructor
  · rintro ⟨leftRelation, hleftStage, rightRelation, hrightStage,
      tupleSpace, hspaceStage, hbody⟩ tuple htuple
    have htupleStage : tuple ∈ LStageZF θ :=
      (LStageZF_isTransitive θ).mem_trans htuple
        (textbookTupleSpace_mem_LStageZF_l hθ hA positiveArity)
    have hBodyAt := hbody tuple htupleStage
    have hBodyAssignment :
        snoc (snoc (snoc (snoc
          ![A, B, natCode positiveArity, natCode code]
          leftRelation) rightRelation) tupleSpace) tuple =
        ![A, B, natCode positiveArity, natCode code,
          leftRelation, rightRelation, tupleSpace, tuple] := by
      funext position
      fin_cases position <;> rfl
    rw [hBodyAssignment] at hBodyAt
    simp only [textbookEStageAgreementBody_l,
      Constructible.Model.SatisfiesIn,
      Constructible.Model.satisfiesIn_imp_iff,
      Constructible.Model.satisfiesIn_biimp_iff] at hBodyAt
    rcases hBodyAt with ⟨hLeft, hRight, hSpace, hAgreement⟩
    have hFullAssignment : ∀ position : Fin 8,
        ![A, B, natCode positiveArity, natCode code,
          leftRelation, rightRelation, tupleSpace, tuple] position ∈
          LStageZF θ := by
      intro position
      fin_cases position
      · exact hA
      · exact hB
      · exact natCode_mem_LStageZF_of_isSuccLimit hθ positiveArity
      · exact natCode_mem_LStageZF_of_isSuccLimit hθ code
      · exact hleftStage
      · exact hrightStage
      · exact hspaceStage
      · exact htupleStage
    have hLeftValue :=
      (satisfiesIn_textbookEBoundedValueFormulaAt_natCode_iff_l
        hθ hω (0 : Fin 8) (2 : Fin 8) (3 : Fin 8) (4 : Fin 8)
        ![A, B, natCode positiveArity, natCode code,
          leftRelation, rightRelation, tupleSpace, tuple]
        hFullAssignment positiveArity code rfl rfl).mp hLeft
    have hRightValue :=
      (satisfiesIn_textbookEBoundedValueFormulaAt_natCode_iff_l
        hθ hω (1 : Fin 8) (2 : Fin 8) (3 : Fin 8) (5 : Fin 8)
        ![A, B, natCode positiveArity, natCode code,
          leftRelation, rightRelation, tupleSpace, tuple]
        hFullAssignment positiveArity code rfl rfl).mp hRight
    change leftRelation = textbookEZF A (natCode positiveArity)
      (natCode code) at hLeftValue
    change rightRelation = textbookEZF B (natCode positiveArity)
      (natCode code) at hRightValue
    have hSpaceAssignment :
        (fun position =>
          ![A, B, natCode positiveArity, natCode code,
            leftRelation, rightRelation, tupleSpace, tuple]
            (![(0 : Fin 8), (2 : Fin 8), (6 : Fin 8)] position)) =
          ![A, natCode positiveArity, tupleSpace] := by
      funext position
      fin_cases position <;> rfl
    rw [Constructible.Model.finiteTupleSpaceFormulaAt,
      Constructible.Model.satisfiesIn_rename, hSpaceAssignment] at hSpace
    have hSpaceValue :=
      (satisfiesIn_finiteTupleSpaceFormula_stage_natCode_iff_l
        hθ hω positiveArity hA hspaceStage).mp hSpace
    change tuple ∈ tupleSpace →
      (tuple ∈ leftRelation ↔ tuple ∈ rightRelation) at hAgreement
    rw [hLeftValue, hRightValue] at hAgreement
    exact hAgreement (by simpa only [hSpaceValue] using htuple)
  · intro hAgreement
    let leftRelation := textbookEZF A (natCode positiveArity) (natCode code)
    let rightRelation := textbookEZF B (natCode positiveArity) (natCode code)
    let tupleSpace := textbookTupleSpace A positiveArity
    have hleftStage : leftRelation ∈ LStageZF θ :=
      textbookEZF_mem_LStageZF_l hθ hA positiveArity code
    have hrightStage : rightRelation ∈ LStageZF θ :=
      textbookEZF_mem_LStageZF_l hθ hB positiveArity code
    have hspaceStage : tupleSpace ∈ LStageZF θ :=
      textbookTupleSpace_mem_LStageZF_l hθ hA positiveArity
    refine ⟨leftRelation, hleftStage, rightRelation, hrightStage,
      tupleSpace, hspaceStage, ?_⟩
    intro tuple htupleStage
    have hBodyAssignment :
        snoc (snoc (snoc (snoc
          ![A, B, natCode positiveArity, natCode code]
          leftRelation) rightRelation) tupleSpace) tuple =
        ![A, B, natCode positiveArity, natCode code,
          leftRelation, rightRelation, tupleSpace, tuple] := by
      funext position
      fin_cases position <;> rfl
    rw [hBodyAssignment]
    simp only [textbookEStageAgreementBody_l,
      Constructible.Model.SatisfiesIn,
      Constructible.Model.satisfiesIn_imp_iff,
      Constructible.Model.satisfiesIn_biimp_iff]
    have hFullAssignment : ∀ position : Fin 8,
        ![A, B, natCode positiveArity, natCode code,
          leftRelation, rightRelation, tupleSpace, tuple] position ∈
          LStageZF θ := by
      intro position
      fin_cases position
      · exact hA
      · exact hB
      · exact natCode_mem_LStageZF_of_isSuccLimit hθ positiveArity
      · exact natCode_mem_LStageZF_of_isSuccLimit hθ code
      · exact hleftStage
      · exact hrightStage
      · exact hspaceStage
      · exact htupleStage
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (satisfiesIn_textbookEBoundedValueFormulaAt_natCode_iff_l
        hθ hω (0 : Fin 8) (2 : Fin 8) (3 : Fin 8) (4 : Fin 8)
        ![A, B, natCode positiveArity, natCode code,
          leftRelation, rightRelation, tupleSpace, tuple]
        hFullAssignment positiveArity code rfl rfl).mpr rfl
    · exact (satisfiesIn_textbookEBoundedValueFormulaAt_natCode_iff_l
        hθ hω (1 : Fin 8) (2 : Fin 8) (3 : Fin 8) (5 : Fin 8)
        ![A, B, natCode positiveArity, natCode code,
          leftRelation, rightRelation, tupleSpace, tuple]
        hFullAssignment positiveArity code rfl rfl).mpr rfl
    · rw [Constructible.Model.finiteTupleSpaceFormulaAt,
        Constructible.Model.satisfiesIn_rename]
      have hSpaceAssignment :
          (fun position =>
            ![A, B, natCode positiveArity, natCode code,
              leftRelation, rightRelation, tupleSpace, tuple]
              (![(0 : Fin 8), (2 : Fin 8), (6 : Fin 8)] position)) =
            ![A, natCode positiveArity, tupleSpace] := by
        funext position
        fin_cases position <;> rfl
      rw [hSpaceAssignment]
      exact (satisfiesIn_finiteTupleSpaceFormula_stage_natCode_iff_l
        hθ hω positiveArity hA hspaceStage).mpr rfl
    · change tuple ∈ tupleSpace →
        (tuple ∈ leftRelation ↔ tuple ∈ rightRelation)
      intro htuple
      exact hAgreement tuple (by simpa only [tupleSpace] using htuple)

end

end YesMetaZFC.BMS.ConstructibleBridge
