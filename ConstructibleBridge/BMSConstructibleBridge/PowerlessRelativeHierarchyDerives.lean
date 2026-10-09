import BMSConstructibleBridge.PowerlessRelativeLevelCorrespondence

/-! # 纯相对历史与层值唯一性的原 Z₂ 推导

存在句显式保留传递基集、实际序数条件。正式出口是这些纯隶属句的原图
翻译在原 Z₂ 中的 Derives，不是新加的层次公理，也不是最终 BMS 句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeHierarchyDerives

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mk_l mem_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

private abbrev quotient_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) := SecondOrderQuotient.structure_l hℳ

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def transitive_m {Γ Δ : SortContext ℒ} (B : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up B)) <|
    .forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here)))
      (SecondOrderObjectSyntax.member_m (.bvar .here) (up (up B)))

theorem transitive_formula_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Γ Δ : SortContext ℒ}
    (η : Env (quotient_l hℳ) Γ Δ) (B : Term ℒ Γ Δ .set) :
    (transitive_m B).satisfies η ↔ ∀ x, mem_l hℳ x (B.eval η) → ∀ y, mem_l hℳ y x → mem_l hℳ y (B.eval η) := by
  simp only [transitive_m, up, Formula.satisfies, SecondOrderObjectSyntax.member_m,
    Arguments.eval, Term.eval, Term.eval_weakenBound]
  rfl

theorem base_code_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    ∃ W : SecondOrderModel.set_l ℳ, ∃ hW : SecondOrderDomain.wf_l W (SecondOrderModel.zero_l ℳ),
      mk_l hℳ ⟨W, SecondOrderModel.zero_l ℳ, hW⟩ = B ∧
        SecondOrderTransitiveSuperset.transitive_l ⟨W, SecondOrderModel.zero_l ℳ, hW⟩ := by
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ B
  obtain ⟨W, hW, hWA⟩ := SecondOrderRootNormalization.normal_exists_l hℳ A
  let C : SecondOrderGraph.code_l ℳ := ⟨W, SecondOrderModel.zero_l ℳ, hW⟩
  have hEq : mk_l hℳ C = mk_l hℳ A := (SecondOrderQuotient.eq_iff_l hℳ C A).mpr hWA
  refine ⟨W, hW, hEq, ?_⟩
  intro X Y hX hYX
  change mem_l hℳ (mk_l hℳ Y) (mk_l hℳ C)
  change mem_l hℳ (mk_l hℳ X) (mk_l hℳ C) at hX
  rw [hEq] at hX ⊢
  exact hBase (mk_l hℳ X) hX (mk_l hℳ Y) hYX

def existence_m {Γ Δ : SortContext ℒ} (B A : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .imp (transitive_m B) <| .imp (PowerlessRelativeHierarchySyntax.ordinal_m A) <|
    .existsE .set <| .existsE .set <|
      PowerlessRelativeHierarchySyntax.history_m (up (up B)) (up (up A)) (.bvar (.there .here)) (.bvar .here)

def existence_schema_m : Formula ℒ [] [.set, .set] := existence_m (.fvar .here) (.fvar (.there .here))

def existence_sentence_m : Sentence ℒ := Metatheory.Formula.forall_close existence_schema_m

theorem existence_formula_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (K : source_coding_l hℳ)
    {Γ Δ : SortContext ℒ} (η : Env (quotient_l hℳ) Γ Δ) (B A : Term ℒ Γ Δ .set) :
    (existence_m B A).satisfies η := by
  intro hTrans hOrd
  have hBase := (transitive_formula_l hℳ η B).mp hTrans
  have hA := (PowerlessRelativeHierarchySemantics.ordinal_formula_l (hℳ := hℳ) η A).mp hOrd
  obtain ⟨W, hW, hWB, hWTrans⟩ := base_code_l hℳ (B.eval η) hBase
  obtain ⟨A₀, hA₀⟩ := SecondOrderQuotient.surj_l hℳ (A.eval η)
  rw [← hA₀] at hA
  obtain ⟨f, r, hHistory⟩ := PowerlessRelativeHierarchyRealization.exists_l hℳ W hW hWTrans A₀ hA
  rw [hWB, hA₀] at hHistory
  refine ⟨f, r, ?_⟩
  apply (PowerlessRelativeHierarchySemantics.history_formula_l K ((η.pushBound f).pushBound r)
    (up (up B)) (up (up A)) (.bvar (.there .here)) (.bvar .here)).mpr
  simp only [up, Term.eval_weakenBound]
  simpa only [Term.eval, Env.pushBound, Assignment.push] using hHistory

def uniqueness_m {Γ Δ : SortContext ℒ} (B a y z : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .imp (.conj (PowerlessRelativeHierarchySyntax.level_m B a y)
    (PowerlessRelativeHierarchySyntax.level_m B a z)) (.equal y z)

def uniqueness_schema_m : Formula ℒ [] [.set, .set, .set, .set] :=
  uniqueness_m (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here))))

def uniqueness_sentence_m : Sentence ℒ := Metatheory.Formula.forall_close uniqueness_schema_m

theorem uniqueness_formula_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (K : source_coding_l hℳ)
    {Γ Δ : SortContext ℒ} (η : Env (quotient_l hℳ) Γ Δ) (B a y z : Term ℒ Γ Δ .set) :
    (uniqueness_m B a y z).satisfies η := by
  rintro ⟨hy, hz⟩
  exact PowerlessRelativeHierarchyAgreement.level_unique_l hℳ
    ((PowerlessRelativeHierarchySemantics.level_formula_l K η B a y).mp hy)
    ((PowerlessRelativeHierarchySemantics.level_formula_l K η B a z).mp hz)

theorem existence_models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    existence_sentence_m.TrueIn (quotient_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  exact existence_formula_l hℳ K η _ _

theorem uniqueness_models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    uniqueness_sentence_m.TrueIn (quotient_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  exact uniqueness_formula_l hℳ K η _ _ _ _

theorem exists_derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m existence_sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => existence_models_l hℳ)

theorem unique_derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m uniqueness_sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => uniqueness_models_l hℳ)

#print axioms exists_derives_m
#print axioms unique_derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeHierarchyDerives
