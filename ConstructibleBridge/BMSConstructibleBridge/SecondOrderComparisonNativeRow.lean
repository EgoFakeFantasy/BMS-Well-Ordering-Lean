import BMSConstructibleBridge.SecondOrderComparisonHistoryStage
import BMSConstructibleBridge.SecondOrderNativeRowFormula

/-! # 实际三分支比较行的原二阶正文

原自由变量依次为输出实数、阶段数、候选历史实数及固定参数。所有图码都
显式给定或由正文存在量词取得，没有 Type 层选择。总唯一性来自已证明的
真实层次方程，不能据此宣称比较历史的良序保持或最终 BMS 推导已经完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonNativeRow

open Logic FirstOrder SecondOrderSyntax SecondOrderInterpretation PowerlessBMSQuotientCoding
open ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l GraphTranslation.context_m

universe u

def context_m : SortContext ℒ := [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set]

def template_m : Formula ℒ [] (.set :: .set :: .set :: context_m) :=
  let ω : Term ℒ [] (.set :: .set :: .set :: context_m) .set := .fvar (.there (.there (.there (.here))))
  let e : Term ℒ [] (.set :: .set :: .set :: context_m) .set := .fvar (.there (.there (.there (.there (.here)))))
  let t₁ : Term ℒ [] (.set :: .set :: .set :: context_m) .set := .fvar (.there (.there (.there (.there (.there (.here))))))
  let t₂ : Term ℒ [] (.set :: .set :: .set :: context_m) .set := .fvar (.there (.there (.there (.there (.there (.there (.here)))))))
  let t₃ : Term ℒ [] (.set :: .set :: .set :: context_m) .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.here))))))))
  let Pair : Term ℒ [] (.set :: .set :: .set :: context_m) .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))
  let Valid : Term ℒ [] (.set :: .set :: .set :: context_m) .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))
  let I : Term ℒ [] (.set :: .set :: .set :: context_m) .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))
  let J : Term ℒ [] (.set :: .set :: .set :: context_m) .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))
  let T : Term ℒ [] (.set :: .set :: .set :: context_m) .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))))
  let P₀ : Term ℒ [] (.set :: .set :: .set :: context_m) .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))))
  let f : Term ℒ [] (.set :: .set :: .set :: context_m) .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))))))
  let C : Term ℒ [] (.set :: .set :: .set :: context_m) .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))))))
  SecondOrderComparisonHistoryStage.output_m ω e t₁ t₂ t₃ Pair Valid I J T P₀ f C
    (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)

def formula_m : Formula signature_m [] (.set :: .num :: .set :: .set :: GraphTranslation.context_m context_m) :=
  SecondOrderNativeRowFormula.formula_m template_m

theorem pure_m : SecondOrderArithmetic.language_m formula_m = true :=
  SecondOrderNativeRowFormula.pure_m template_m

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 参数码均显式传入，不按模型选择规范码。 -/
structure parameters_l (ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m) where
  ω : SecondOrderGraph.code_l ℳ
  e : SecondOrderGraph.code_l ℳ
  t₁ : SecondOrderGraph.code_l ℳ
  t₂ : SecondOrderGraph.code_l ℳ
  t₃ : SecondOrderGraph.code_l ℳ
  Pair : SecondOrderGraph.code_l ℳ
  Valid : SecondOrderGraph.code_l ℳ
  I : SecondOrderGraph.code_l ℳ
  J : SecondOrderGraph.code_l ℳ
  T : SecondOrderGraph.code_l ℳ
  P₀ : SecondOrderGraph.code_l ℳ
  f : SecondOrderGraph.code_l ℳ
  C : SecondOrderGraph.code_l ℳ

private def empty_l : assignment_l ℳ [] := fun v => nomatch v

def assignment_l (p : parameters_l ℳ) : SecondOrderInterpretation.assignment_l ℳ context_m :=
  push_l p.ω (push_l p.e (push_l p.t₁ (push_l p.t₂ (push_l p.t₃ (push_l p.Pair (push_l p.Valid (push_l p.I (push_l p.J (push_l p.T (push_l p.P₀ (push_l p.f (push_l p.C (empty_l)))))))))))))

def source_l (p : parameters_l ℳ) : Env 𝒱 [] context_m :=
  SecondOrderInterpretation.source_l hℳ empty_l (assignment_l p)

def row_l (p : parameters_l ℳ) (i H W : type_l hℳ) : Prop :=
  SecondOrderComparisonHistoryStage.output_l (SecondOrderQuotient.mk_l hℳ p.ω) (SecondOrderQuotient.mk_l hℳ p.e) (SecondOrderQuotient.mk_l hℳ p.t₁) (SecondOrderQuotient.mk_l hℳ p.t₂) (SecondOrderQuotient.mk_l hℳ p.t₃) (SecondOrderQuotient.mk_l hℳ p.Pair) (SecondOrderQuotient.mk_l hℳ p.Valid) (SecondOrderQuotient.mk_l hℳ p.I) (SecondOrderQuotient.mk_l hℳ p.J) (SecondOrderQuotient.mk_l hℳ p.T) (SecondOrderQuotient.mk_l hℳ p.P₀) (SecondOrderQuotient.mk_l hℳ p.f) (SecondOrderQuotient.mk_l hℳ p.C) i H W

theorem template_formula_l (p : parameters_l ℳ) (i H W : type_l hℳ) :
    template_m.satisfies ((((source_l p).pushFree H).pushFree i).pushFree W) ↔ row_l p i H W := by
  exact SecondOrderComparisonHistoryStage.output_formula_l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

def environment_l (K : source_coding_l hℳ) (p : parameters_l ℳ) :
    Env ℳ [] (.set :: GraphTranslation.context_m context_m) :=
  SecondOrderNativeRowFormula.parameters_l K (assignment_l p)

theorem formula_l (K : source_coding_l hℳ) (p : parameters_l ℳ)
    (n : SecondOrderModel.num_l ℳ) (H W : SecondOrderModel.set_l ℳ) :
    formula_m.satisfies ((((environment_l K p).pushFree H).pushFree n).pushFree W) ↔
      ∃ A B : SecondOrderGraph.code_l ℳ,
        SecondOrderRealTraceSyntax.trace_l K.less A.real A.root H ∧
        SecondOrderRealTraceSyntax.trace_l K.less B.real B.root W ∧
          row_l p (numberCode_l K n).val (SecondOrderQuotient.mk_l hℳ A) (SecondOrderQuotient.mk_l hℳ B) := by
  rw [formula_m, environment_l, SecondOrderNativeRowFormula.formula_l]
  constructor
  · rintro ⟨A, hA, B, hB, hBody⟩
    exact ⟨A, B, hA, hB, (template_formula_l p _ _ _).mp hBody⟩
  · rintro ⟨A, B, hA, hB, hBody⟩
    exact ⟨A, hA, B, hB, (template_formula_l p _ _ _).mpr hBody⟩

/-- 实际编码包与实际层次方程给出原二阶全部候选历史上的唯一行。 -/
theorem exists_unique_l (K : source_coding_l hℳ) (p : parameters_l ℳ)
    (hω : SecondOrderQuotient.mk_l hℳ p.ω = K.omega)
    (he : SecondOrderQuotient.mk_l hℳ p.e = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    {A B F r : type_l hℳ}
    (hCoding : SecondOrderComparisonStageTotal.coding_l K
      (SecondOrderQuotient.mk_l hℳ p.t₁) (SecondOrderQuotient.mk_l hℳ p.t₂)
      (SecondOrderQuotient.mk_l hℳ p.t₃) (SecondOrderQuotient.mk_l hℳ p.Pair) (SecondOrderQuotient.mk_l hℳ p.Valid))
    (hA : SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) A)
    (hJ : map_l (ℳ := 𝒱) (SecondOrderQuotient.mk_l hℳ p.J) (SecondOrderQuotient.mk_l hℳ p.I) A)
    (hInject : injective_l (ℳ := 𝒱) (SecondOrderQuotient.mk_l hℳ p.J))
    (hOnto : ∀ a, mem_l hℳ a A → ∃ i, mem_l hℳ i (SecondOrderQuotient.mk_l hℳ p.I) ∧
      value_l (ℳ := 𝒱) (SecondOrderQuotient.mk_l hℳ p.J) i a)
    (hI : subset_l (ℳ := 𝒱) (SecondOrderQuotient.mk_l hℳ p.I) K.omega)
    (hTMap : map_l (ℳ := 𝒱) (SecondOrderQuotient.mk_l hℳ p.T) (SecondOrderQuotient.mk_l hℳ p.I) r)
    (hF : PowerlessRelativeHierarchySemantics.history_l hℳ B A F r)
    (hT : ∀ i X, value_l (ℳ := 𝒱) (SecondOrderQuotient.mk_l hℳ p.T) i X ↔
      ∃ a, value_l (ℳ := 𝒱) (SecondOrderQuotient.mk_l hℳ p.J) i a ∧ value_l (ℳ := 𝒱) F a X)
    (H : SecondOrderModel.set_l ℳ) (n : SecondOrderModel.num_l ℳ) :
    ∃! W : SecondOrderModel.set_l ℳ,
      formula_m.satisfies ((((environment_l K p).pushFree H).pushFree n).pushFree W) := by
  apply SecondOrderNativeRowFormula.exists_unique_l template_m K (assignment_l p) H n
  · intro U V hBody
    have hRow := (template_formula_l p _ _ _).mp hBody
    rw [row_l, hω, he] at hRow
    exact hRow.1
  · intro U V hBody
    have hRow := (template_formula_l p _ _ _).mp hBody
    rw [row_l, hω, he] at hRow
    exact SecondOrderComparisonHistoryStage.guard_l K hRow
  · intro U hU
    let S : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega := ⟨SecondOrderQuotient.mk_l hℳ U, hU⟩
    obtain ⟨R, hR⟩ := PowerlessBMSQuotientReals.trace_exists_l K S
    obtain ⟨W, hW, hOnly⟩ := SecondOrderComparisonHistoryStage.exists_unique_l
      (P₀ := SecondOrderQuotient.mk_l hℳ p.P₀) (f := SecondOrderQuotient.mk_l hℳ p.f)
      (C := SecondOrderQuotient.mk_l hℳ p.C) K hCoding hA hJ hInject hOnto hI hTMap hF hT S R hR (numberCode_l K n).val
    refine ⟨W, (template_formula_l p _ _ _).mpr ?_, ?_⟩
    · simpa only [row_l, hω, he] using hW
    · intro X hX
      apply hOnly X
      have hRow := (template_formula_l p _ _ _).mp hX
      simpa only [row_l, hω, he] using hRow

#print axioms pure_m
#print axioms formula_l
#print axioms exists_unique_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonNativeRow
