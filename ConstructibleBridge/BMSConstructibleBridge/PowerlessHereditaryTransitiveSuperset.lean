import BMSConstructibleBridge.PowerlessHereditaryExtension

/-! # 遗传类内部的传递超集

定义给出的类内可数包络 T 未必已经属于遗传类。用单点扩张将 T 自身
放进另一个可数传递包络，再回传其成员证书，才得到真正的类内传递超集。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryTransitiveSuperset

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

theorem exists_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {B X : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hX : PowerlessHereditaryClass.member_l hℳ B X) : ∃ T,
      PowerlessHereditaryClass.member_l hℳ B T ∧ mem_l hℳ X T ∧
        ∀ x, mem_l hℳ x T → ∀ y, mem_l hℳ y x → mem_l hℳ y T := by
  obtain ⟨T, f, w, hT, hf, hXT, hTrans, hω, hMap, hOnto⟩ := hX
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  let T' : PowerlessRelativeClassStructure.type_l hℳ B := ⟨T, hT⟩
  let f' : PowerlessRelativeClassStructure.type_l hℳ B := ⟨f, hf⟩
  let w' : PowerlessRelativeClassStructure.type_l hℳ B := ⟨w,
    PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase (SecondOrderOmegaOrdinal.ordinal_l hℳ hω)⟩
  have hHereditary := (PowerlessHereditaryClassInternals.correspondence_l (hBase := hBase) T').mpr
    (PowerlessHereditaryExtension.exists_l w' T' T' f'
      ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) w').mpr hω)
      ((PowerlessHereditaryClassInternals.transitive_l (hBase := hBase) T').mpr hTrans)
      (fun _ hx => hx)
      ((PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f' w' T').mpr hMap)
      ((PowerlessRelativeClassFunctionAbsolute.onto_l (hBase := hBase) f' w' T').mpr hOnto))
  exact ⟨T, hHereditary, hXT, hTrans⟩

def closure_m {Γ Δ : SortContext ℒ} (B X : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .conj (PowerlessHereditaryClass.formula_m (up B) (.bvar .here)) <|
    .conj (SecondOrderObjectSyntax.member_m (up X) (.bvar .here))
      (PowerlessRelativeHierarchyDerives.transitive_m (.bvar .here))

theorem closure_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (B X : Term ℒ Γ Δ .set) :
    (closure_m B X).satisfies η ↔ ∃ T, PowerlessHereditaryClass.member_l hℳ (B.eval η) T ∧
      mem_l hℳ (X.eval η) T ∧ ∀ x, mem_l hℳ x T → ∀ y, mem_l hℳ y x → mem_l hℳ y T := by
  simp only [closure_m, Formula.satisfies, PowerlessHereditaryClass.formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval,
    PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m : Formula ℒ [] [.set, .set] :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m (.fvar .here)) <|
    .imp (PowerlessHereditaryClass.formula_m (.fvar .here) (.fvar (.there .here)))
      (closure_m (.fvar .here) (.fvar (.there .here)))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hBase hX
  exact (closure_formula_l K η (.fvar .here) (.fvar (.there .here))).mpr
    (exists_l hℳ ((PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ η (.fvar .here)).mp hBase)
      ((PowerlessHereditaryClass.formula_l K η (.fvar .here) (.fvar (.there .here))).mp hX))

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryTransitiveSuperset
