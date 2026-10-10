import BMSConstructibleBridge.SecondOrderPredecessorCorrespondence
import BMSConstructibleBridge.SecondOrderFormulaArguments

/-! # 双向前驱对应的对象公式

三个实数参数分别表示源关系、目标关系与配对关系。所有覆盖和唯一性均在
原模型自然数索引上量化，没有函数常元或隐含的选择公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPredecessorCorrespondenceFormula

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private def source_m {Γ : SortContext signature_m} : Term signature_m Γ [.set, .set, .set] .set :=
  .fvar (.there (.there .here))

private def target_m {Γ : SortContext signature_m} : Term signature_m Γ [.set, .set, .set] .set :=
  .fvar (.there .here)

private def pairing_m {Γ : SortContext signature_m} : Term signature_m Γ [.set, .set, .set] .set :=
  .fvar .here

private def edges_m : Formula signature_m [] [.set, .set, .set] :=
  .forallE .num <| .forallE .num <| .forallE .num <| .forallE .num <| .imp
    (GraphSyntax.edge_m pairing_m (.bvar (.there (.there (.there .here)))) (.bvar (.there .here))) <|
    .imp (GraphSyntax.edge_m pairing_m (.bvar (.there (.there .here))) (.bvar .here)) <|
    .conj
      (.imp (GraphSyntax.edge_m source_m (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here))))
        (GraphSyntax.edge_m target_m (.bvar (.there .here)) (.bvar .here)))
      (.imp (GraphSyntax.edge_m target_m (.bvar (.there .here)) (.bvar .here))
        (GraphSyntax.edge_m source_m (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here)))))

private def rightUnique_m : Formula signature_m [] [.set, .set, .set] :=
  .forallE .num <| .forallE .num <| .forallE .num <| .imp
    (GraphSyntax.edge_m pairing_m (.bvar (.there (.there .here))) (.bvar (.there .here))) <|
    .imp (GraphSyntax.edge_m pairing_m (.bvar (.there (.there .here))) (.bvar .here))
      (.equal (.bvar (.there .here)) (.bvar .here))

private def leftUnique_m : Formula signature_m [] [.set, .set, .set] :=
  .forallE .num <| .forallE .num <| .forallE .num <| .imp
    (GraphSyntax.edge_m pairing_m (.bvar (.there (.there .here))) (.bvar .here)) <|
    .imp (GraphSyntax.edge_m pairing_m (.bvar (.there .here)) (.bvar .here))
      (.equal (.bvar (.there (.there .here))) (.bvar (.there .here)))

private def forth_m : Formula signature_m [] [.set, .set, .set] :=
  .forallE .num <| .forallE .num <| .imp
    (GraphSyntax.edge_m pairing_m (.bvar (.there .here)) (.bvar .here)) <|
    .forallE .num <| .imp
      (GraphSyntax.edge_m source_m (.bvar .here) (.bvar (.there (.there .here)))) <|
      .existsE .num <| .conj
        (GraphSyntax.edge_m target_m (.bvar .here) (.bvar (.there (.there .here))))
        (GraphSyntax.edge_m pairing_m (.bvar (.there .here)) (.bvar .here))

private def back_m : Formula signature_m [] [.set, .set, .set] :=
  .forallE .num <| .forallE .num <| .imp
    (GraphSyntax.edge_m pairing_m (.bvar (.there .here)) (.bvar .here)) <|
    .forallE .num <| .imp
      (GraphSyntax.edge_m target_m (.bvar .here) (.bvar (.there .here))) <|
      .existsE .num <| .conj
        (GraphSyntax.edge_m source_m (.bvar .here) (.bvar (.there (.there (.there .here)))))
        (GraphSyntax.edge_m pairing_m (.bvar .here) (.bvar (.there .here)))

def template_m : Formula signature_m [] [.set, .set, .set] :=
  .conj edges_m (.conj rightUnique_m (.conj leftUnique_m (.conj forth_m back_m)))

theorem template_pure_m : language_m template_m = true := by rfl

def formula_m {Γ Δ : SortContext signature_m} (R R' I : Term signature_m Γ Δ .set) :
    Formula signature_m Γ Δ :=
  SecondOrderFormulaArguments.formula_m template_m (.cons I (.cons R' (.cons R .nil)))

theorem pure_m {Γ Δ : SortContext signature_m} (R R' I : Term signature_m Γ Δ .set)
    (hR : pure_term_m R = true) (hR' : pure_term_m R' = true) (hI : pure_term_m I = true) :
    language_m (formula_m R R' I) = true :=
  SecondOrderFormulaArguments.pure_m template_m _ template_pure_m
    (by simp only [pure_args_m, hI, hR', hR, Bool.true_and])

theorem template_formula_l (R R' I : set_l ℳ) :
    template_m.satisfies ((((Env.empty (M := ℳ)).pushFree R).pushFree R').pushFree I) ↔
      SecondOrderPredecessorCorrespondence.spec_l R R' I := by
  simp only [template_m, edges_m, rightUnique_m, leftUnique_m, forth_m, back_m,
    Formula.satisfies, SecondOrderPairing.edge_l, source_m, target_m, pairing_m, Term.eval]
  constructor
  · intro h
    exact ⟨fun i j a b hi hj => ⟨(h.1 i j a b hi hj).1, (h.1 i j a b hi hj).2⟩,
      h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  · intro h
    exact ⟨fun i j a b hi hj => ⟨(h.edges i j a b hi hj).mp, (h.edges i j a b hi hj).mpr⟩,
      h.rightUnique, h.leftUnique, h.forth, h.back⟩

theorem formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (R R' I : Term signature_m Γ Δ .set) :
    (formula_m R R' I).satisfies η ↔
      SecondOrderPredecessorCorrespondence.spec_l (R.eval η) (R'.eval η) (I.eval η) := by
  rw [formula_m, SecondOrderFormulaArguments.formula_l]
  have hEnv : SecondOrderRelationSpecification.parameters_l η
      (Automation.RelationalTranslation.argumentsSubstitution (.cons I (.cons R' (.cons R .nil)))) =
      (((Env.empty (M := ℳ)).pushFree (R.eval η)).pushFree (R'.eval η)).pushFree (I.eval η) := by
    apply Env.ext (bound := []) (fun {_} v => nomatch v)
    · intro s v
      cases v with
      | here => rfl
      | there v => cases v with
        | here => rfl
        | there v => cases v with
          | here => rfl
          | there v => nomatch v
  rw [hEnv]
  exact template_formula_l _ _ _

#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPredecessorCorrespondenceFormula
