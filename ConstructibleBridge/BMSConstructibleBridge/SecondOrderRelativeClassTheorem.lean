import BMSConstructibleBridge.SecondOrderRelativeClassFormula

/-! # 相对并类的原 Z₂ 闭包句

传递闭包与基集成员覆盖是实际二阶句的正式推导；这里不宣称相对并类满足
收集公理，也不将它与内部可数的 HCL 混同。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeClassTheorem

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private def zero_m {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .zero .nil

def transitive_m {Γ Δ : SortContext signature_m} (B X Y : Term signature_m Γ Δ .set)
    (rX rY : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .imp (GraphTranslation.domain_m B zero_m) <|
    .imp (GraphTranslation.domain_m X rX) <|
    .imp (GraphTranslation.domain_m Y rY) <|
    .imp (SecondOrderRelativeClassFormula.formula_m B X rX) <|
    .imp (GraphTranslation.atom_m GraphSyntax.mem_m Y X rY rX)
      (SecondOrderRelativeClassFormula.formula_m B Y rY)

def transitive_schema_m : Formula signature_m [] [.set, .set, .set, .num, .num] :=
  transitive_m (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))

def transitive_sentence_m : Sentence signature_m := Metatheory.Formula.forall_close transitive_schema_m

theorem transitive_formula_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (B X Y : Term signature_m Γ Δ .set) (rX rY : Term signature_m Γ Δ .num) :
    (transitive_m B X Y rX rY).satisfies η := by
  intro hB hX hY hClass hYX
  have hBwf : SecondOrderDomain.wf_l (B.eval η) (zero_l ℳ) :=
    (SecondOrderInterpretation.domain_l η B zero_m).mp hB
  have hXwf := (SecondOrderInterpretation.domain_l η X rX).mp hX
  have hYwf := (SecondOrderInterpretation.domain_l η Y rY).mp hY
  have hClassX := (SecondOrderRelativeClassFormula.formula_l hℳ η B X rX hBwf hXwf).mp hClass
  have hMember := (SecondOrderInterpretation.mem_l η Y X rY rX).mp hYX
  exact (SecondOrderRelativeClassFormula.formula_l hℳ η B Y rY hBwf hYwf).mpr
    (SecondOrderRelativeClass.transitive_l hℳ hClassX hMember)

def base_m {Γ Δ : SortContext signature_m} (B X : Term signature_m Γ Δ .set)
    (rX : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .imp (GraphTranslation.domain_m B zero_m) <|
    .imp (SecondOrderGraphTransitivityFormula.formula_m B zero_m) <|
    .imp (GraphTranslation.domain_m X rX) <|
    .imp (GraphTranslation.atom_m GraphSyntax.mem_m X B rX zero_m)
      (SecondOrderRelativeClassFormula.formula_m B X rX)

def base_schema_m : Formula signature_m [] [.set, .set, .num] :=
  base_m (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))

def base_sentence_m : Sentence signature_m := Metatheory.Formula.forall_close base_schema_m

theorem base_formula_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (B X : Term signature_m Γ Δ .set) (rX : Term signature_m Γ Δ .num) :
    (base_m B X rX).satisfies η := by
  intro hB hTrans hX hXB
  have hBwf : SecondOrderDomain.wf_l (B.eval η) (zero_l ℳ) :=
    (SecondOrderInterpretation.domain_l η B zero_m).mp hB
  have hTransB := (SecondOrderGraphTransitivityFormula.formula_l hℳ η B zero_m hBwf).mp hTrans
  have hXwf := (SecondOrderInterpretation.domain_l η X rX).mp hX
  exact (SecondOrderRelativeClassFormula.formula_l hℳ η B X rX hBwf hXwf).mpr
    (SecondOrderRelativeClass.base_l hℳ (B.eval η) hBwf hTransB
      ⟨X.eval η, rX.eval η, hXwf⟩ ((SecondOrderInterpretation.mem_l η X B rX zero_m).mp hXB))

theorem transitive_derives_m : Derives theory_m [] transitive_sentence_m := by
  apply SecondOrderCompleteness.derives_m
  intro ℳ hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  exact transitive_formula_l hℳ η _ _ _ _ _

theorem base_derives_m : Derives theory_m [] base_sentence_m := by
  apply SecondOrderCompleteness.derives_m
  intro ℳ hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  exact base_formula_l hℳ η _ _ _

#print axioms transitive_derives_m
#print axioms base_derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeClassTheorem
