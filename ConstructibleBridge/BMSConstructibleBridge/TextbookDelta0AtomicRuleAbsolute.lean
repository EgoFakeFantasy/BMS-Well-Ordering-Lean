import BMSConstructibleBridge.TextbookNaturalArithmeticStage
import BMSConstructibleBridge.TextbookDelta0AtomicRule

/-!
# 原子分类规则在可构造层中的语义

原子规则的内部见证全是标准自然数。前一模块给出的 E-code 层内语义因此足以
把局部满足关系规范化为两个有界变量索引，并反向在 `L_omega` 中重建见证。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

private theorem satisfiesIn_disj_atomic_iff
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (assignment : Tuple ZFSet.{u} n) :
    Model.SatisfiesIn M (FOFormula.disj left right) assignment ↔
      Model.SatisfiesIn M left assignment ∨
        Model.SatisfiesIn M right assignment := by
  classical
  simp only [FOFormula.disj, Model.SatisfiesIn]
  tauto

/-- 原子规则公式在后继极限层中精确表示成员与等号两个原子分支。 -/
theorem satisfiesIn_textbookDelta0AtomicRuleFormula_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (graph position : ZFSet.{u}) (entry : TextbookDelta0Judgment)
    (hGraph : graph ∈ LStageZF θ) (hPosition : position ∈ LStageZF θ) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookDelta0AtomicRuleFormula_l
        ![Ordinal.omega0.toZFSet, graph, position,
          natCode entry.arity, natCode entry.code] ↔
      ∃ left right : Fin entry.arity,
        entry.code = textbookECode left.1 right.1 0 ∨
          entry.code = textbookECode left.1 right.1 1 := by
  let base : Tuple ZFSet.{u} 5 :=
    ![Ordinal.omega0.toZFSet, graph, position,
      natCode entry.arity, natCode entry.code]
  have hBase : Model.TupleIn (LStageZF θ : Set ZFSet.{u}) base := by
    intro index
    fin_cases index
    · exact omega_toZFSet_mem_stage_l hω
    · exact hGraph
    · exact hPosition
    · exact natCode_mem_stage_l hω _
    · exact natCode_mem_stage_l hω _
  simp only [textbookDelta0AtomicRuleFormula_l, Model.SatisfiesIn]
  change (∃ left, left ∈ LStageZF θ ∧
    ∃ right, right ∈ LStageZF θ ∧
    ∃ tag, tag ∈ LStageZF θ ∧
      Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookDelta0AtomicRuleBody_l
        (snoc (snoc (snoc base left) right) tag)) ↔ _
  simp only [textbookDelta0AtomicRuleAssignment_l]
  constructor
  · rintro ⟨leftSet, hLeftStage, rightSet, hRightStage, tagSet, hTagStage,
      hBody⟩
    simp only [textbookDelta0AtomicRuleBody_l, Model.SatisfiesIn,
      satisfiesIn_disj_atomic_iff,
      TextbookNatFormula.satisfiesIn_textbookECodeFormulaAt] at hBody
    rcases hBody with
      ⟨hLeftOmega, hRightOmega, hTagFormula, hCodeFormula,
        hLeftBound, hRightBound⟩
    obtain ⟨left, rfl⟩ :=
      (IndexedSequenceZF.mem_omega_iff_exists_natCode leftSet).mp hLeftOmega
    obtain ⟨right, rfl⟩ :=
      (IndexedSequenceZF.mem_omega_iff_exists_natCode rightSet).mp hRightOmega
    have hLeft : left < entry.arity :=
      (natCode_mem_natCode_iff _ _).mp hLeftBound
    have hRight : right < entry.arity :=
      (natCode_mem_natCode_iff _ _).mp hRightBound
    let leftIndex : Fin entry.arity := ⟨left, hLeft⟩
    let rightIndex : Fin entry.arity := ⟨right, hRight⟩
    rcases hTagFormula with hTagFormula | hTagFormula
    · have hTag : tagSet = (natCode 0 : ZFSet.{u}) :=
        (Model.satisfiesIn_natLiteralDeltaAt_iff
          (LStageZF_isTransitive θ) 0 (7 : Fin 8)
          ![Ordinal.omega0.toZFSet, graph, position,
            natCode entry.arity, natCode entry.code,
            natCode left, natCode right, tagSet] (by
              intro index
              fin_cases index
              · exact omega_toZFSet_mem_stage_l hω
              · exact hGraph
              · exact hPosition
              · exact natCode_mem_stage_l hω _
              · exact natCode_mem_stage_l hω _
              · exact hLeftStage
              · exact hRightStage
              · exact hTagStage)).mp hTagFormula
      subst tagSet
      have hCode : (natCode entry.code : ZFSet.{u}) =
          natCode (textbookECode left right 0) :=
        (satisfiesIn_textbookECodeFormula_stage_natCode_iff_l
          hθ hω left right 0 (natCode_mem_stage_l hω entry.code)).mp
            hCodeFormula
      exact ⟨leftIndex, rightIndex, Or.inl (natCode_injective hCode)⟩
    · have hTag : tagSet = (natCode 1 : ZFSet.{u}) :=
        (Model.satisfiesIn_natLiteralDeltaAt_iff
          (LStageZF_isTransitive θ) 1 (7 : Fin 8)
          ![Ordinal.omega0.toZFSet, graph, position,
            natCode entry.arity, natCode entry.code,
            natCode left, natCode right, tagSet] (by
              intro index
              fin_cases index
              · exact omega_toZFSet_mem_stage_l hω
              · exact hGraph
              · exact hPosition
              · exact natCode_mem_stage_l hω _
              · exact natCode_mem_stage_l hω _
              · exact hLeftStage
              · exact hRightStage
              · exact hTagStage)).mp hTagFormula
      subst tagSet
      have hCode : (natCode entry.code : ZFSet.{u}) =
          natCode (textbookECode left right 1) :=
        (satisfiesIn_textbookECodeFormula_stage_natCode_iff_l
          hθ hω left right 1 (natCode_mem_stage_l hω entry.code)).mp
            hCodeFormula
      exact ⟨leftIndex, rightIndex, Or.inr (natCode_injective hCode)⟩
  · rintro ⟨left, right, hCode | hCode⟩
    · refine ⟨natCode left.1, natCode_mem_stage_l hω _,
        natCode right.1, natCode_mem_stage_l hω _,
        natCode 0, natCode_mem_stage_l hω _, ?_⟩
      simp only [textbookDelta0AtomicRuleBody_l, Model.SatisfiesIn,
        satisfiesIn_disj_atomic_iff,
        TextbookNatFormula.satisfiesIn_textbookECodeFormulaAt]
      refine ⟨(IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr
          ⟨left.1, rfl⟩,
        (IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr
          ⟨right.1, rfl⟩, Or.inl ?_, ?_,
        (natCode_mem_natCode_iff _ _).mpr left.2,
        (natCode_mem_natCode_iff _ _).mpr right.2⟩
      · apply (Model.satisfiesIn_natLiteralDeltaAt_iff
          (LStageZF_isTransitive θ) 0 (7 : Fin 8) _ ?_).mpr
        · rfl
        · intro index
          fin_cases index <;> first
            | exact omega_toZFSet_mem_stage_l hω
            | exact hGraph
            | exact hPosition
            | exact natCode_mem_stage_l hω _
      · apply (satisfiesIn_textbookECodeFormula_stage_natCode_iff_l
          hθ hω left.1 right.1 0 (natCode_mem_stage_l hω entry.code)).mpr
        rw [hCode]
    · refine ⟨natCode left.1, natCode_mem_stage_l hω _,
        natCode right.1, natCode_mem_stage_l hω _,
        natCode 1, natCode_mem_stage_l hω _, ?_⟩
      simp only [textbookDelta0AtomicRuleBody_l, Model.SatisfiesIn,
        satisfiesIn_disj_atomic_iff,
        TextbookNatFormula.satisfiesIn_textbookECodeFormulaAt]
      refine ⟨(IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr
          ⟨left.1, rfl⟩,
        (IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr
          ⟨right.1, rfl⟩, Or.inr ?_, ?_,
        (natCode_mem_natCode_iff _ _).mpr left.2,
        (natCode_mem_natCode_iff _ _).mpr right.2⟩
      · apply (Model.satisfiesIn_natLiteralDeltaAt_iff
          (LStageZF_isTransitive θ) 1 (7 : Fin 8) _ ?_).mpr
        · rfl
        · intro index
          fin_cases index <;> first
            | exact omega_toZFSet_mem_stage_l hω
            | exact hGraph
            | exact hPosition
            | exact natCode_mem_stage_l hω _
      · apply (satisfiesIn_textbookECodeFormula_stage_natCode_iff_l
          hθ hω left.1 right.1 1 (natCode_mem_stage_l hω entry.code)).mpr
        rw [hCode]

/-- 原子规则公式在规范公开参数上对该层绝对。 -/
theorem textbookDelta0AtomicRuleFormula_stage_absolute_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (graph position : ZFSet.{u}) (entry : TextbookDelta0Judgment)
    (hGraph : graph ∈ LStageZF θ) (hPosition : position ∈ LStageZF θ) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookDelta0AtomicRuleFormula_l
        ![Ordinal.omega0.toZFSet, graph, position,
          natCode entry.arity, natCode entry.code] ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        textbookDelta0AtomicRuleFormula_l
        ![Ordinal.omega0.toZFSet, graph, position,
          natCode entry.arity, natCode entry.code] :=
  (satisfiesIn_textbookDelta0AtomicRuleFormula_iff_l
    hθ hω graph position entry hGraph hPosition).trans
      (satisfies_textbookDelta0AtomicRuleFormula_iff_l
        graph position entry).symm

end YesMetaZFC.BMS.ConstructibleBridge
