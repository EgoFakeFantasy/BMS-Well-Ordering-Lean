import BMSConstructibleBridge.PowerlessRelativeClassCorrespondence

/-! # 相对类内可数传递包络的遗传类

可数性的满射集合函数必须本身属于相对类，不能只给环境图商中的满射。
这里只验证定义及遗传传递性的原 Z₂ 推导；尚未证明该类满足 Collection，
亦未声称任意候选实数已经具有所需的类内包络。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryClass

open Logic FirstOrder PowerlessBMSQuotientCoding SecondOrderObjectSyntax
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private abbrev quotient_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) := SecondOrderQuotient.structure_l hℳ

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def body_m {Γ Δ : SortContext ℒ} (B X T f w : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelativeHierarchySyntax.class_m B T) <|
    .conj (PowerlessRelativeHierarchySyntax.class_m B f) <|
      .conj (member_m X T) <| .conj (PowerlessRelativeHierarchyDerives.transitive_m T) <|
        .conj (SecondOrderOmegaSyntax.omega_m w) <| .conj (map_m f w T)
          (PowerlessMemberDefSyntax.onto_m w T f)

def formula_m {Γ Δ : SortContext ℒ} (B X : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <|
    body_m (up (up (up B))) (up (up (up X))) (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

def body_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B X T f w : type_l hℳ) : Prop :=
  PowerlessRelativeClassCorrespondence.member_l hℳ B T ∧
    PowerlessRelativeClassCorrespondence.member_l hℳ B f ∧ mem_l hℳ X T ∧
      (∀ x, mem_l hℳ x T → ∀ y, mem_l hℳ y x → mem_l hℳ y T) ∧
        SecondOrderOmega.omega_l hℳ w ∧ SecondOrderFunctionObjects.map_l hℳ f w T ∧
          ∀ y, mem_l hℳ y T → ∃ x, mem_l hℳ x w ∧ SecondOrderFunctionObjects.value_l hℳ f x y

def member_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B X : type_l hℳ) : Prop :=
  ∃ T f w, body_l hℳ B X T f w

theorem body_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (quotient_l hℳ) Γ Δ) (B X T f w : Term ℒ Γ Δ .set) :
    (body_m B X T f w).satisfies η ↔ body_l hℳ (B.eval η) (X.eval η) (T.eval η) (f.eval η) (w.eval η) := by
  simp only [body_m, Formula.satisfies, PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ, SecondOrderOmegaSyntax.omega_l hℳ,
    SecondOrderObjectSyntax.map_l hℳ, PowerlessMemberDefFormulaSemantics.onto_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  rfl

theorem formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (quotient_l hℳ) Γ Δ) (B X : Term ℒ Γ Δ .set) :
    (formula_m B X).satisfies η ↔ member_l hℳ (B.eval η) (X.eval η) := by
  simp only [formula_m, up, Formula.satisfies, body_formula_l K, Term.eval, Term.eval_weakenBound]
  rfl

theorem transitive_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {B X Y : type_l hℳ}
    (hX : member_l hℳ B X) (hYX : mem_l hℳ Y X) : member_l hℳ B Y := by
  obtain ⟨T, f, w, hT, hf, hXT, hTrans, hω, hMap, hOnto⟩ := hX
  exact ⟨T, f, w, hT, hf, hTrans X hXT Y hYX, hTrans, hω, hMap, hOnto⟩

theorem contained_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {B X : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hX : member_l hℳ B X) : PowerlessRelativeClassCorrespondence.member_l hℳ B X := by
  obtain ⟨T, _, _, hT, _, hXT, _⟩ := hX
  exact PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hT hXT

def schema_m : Formula ℒ [] [.set, .set, .set] :=
  .imp (formula_m (.fvar .here) (.fvar (.there .here))) <|
    .imp (member_m (.fvar (.there (.there .here))) (.fvar (.there .here)))
      (formula_m (.fvar .here) (.fvar (.there (.there .here))))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) : sentence_m.TrueIn (quotient_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hX hYX
  have hX' := (formula_l K η (.fvar .here) (.fvar (.there .here))).mp hX
  exact (formula_l K η (.fvar .here) (.fvar (.there (.there .here)))).mpr (transitive_l hℳ hX' hYX)

theorem transitive_derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryClass
