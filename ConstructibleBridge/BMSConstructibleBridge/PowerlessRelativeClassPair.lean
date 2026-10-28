import BMSConstructibleBridge.PowerlessRelativeClassBounds
import BMSConstructibleBridge.SecondOrderMemberDefPair

/-! # 相对并类的配对及有序对闭包

先将两个参数放入共同层，再在后继 Def 中形成等式析取的精确切片。
结论提供纯集合语言配对句的原 Z₂ 推导，未附加类内可数性或 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassPair

open Logic FirstOrder PowerlessBMSQuotientCoding SecondOrderObjectSyntax
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private abbrev quotient_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) := SecondOrderQuotient.structure_l hℳ

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

theorem pair_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {B X Y P : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hX : PowerlessRelativeClassCorrespondence.member_l hℳ B X)
    (hY : PowerlessRelativeClassCorrespondence.member_l hℳ B Y)
    (hP : SecondOrderPairObjects.pair_l hℳ X Y P) : PowerlessRelativeClassCorrespondence.member_l hℳ B P := by
  obtain ⟨a, c, hc, hXc, hYc⟩ := PowerlessRelativeClassBounds.common_l hℳ hBase hX hY
  obtain ⟨b, d, _, hd, hDef⟩ := PowerlessRelativeLevelClosure.successor_exists_l hℳ hBase hc
  exact ⟨b, d, hd, SecondOrderMemberDefPair.member_l hℳ hDef hXc hYc hP⟩

theorem ordered_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {B X Y P : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hX : PowerlessRelativeClassCorrespondence.member_l hℳ B X)
    (hY : PowerlessRelativeClassCorrespondence.member_l hℳ B Y)
    (hP : SecondOrderPairObjects.ordered_l hℳ X Y P) : PowerlessRelativeClassCorrespondence.member_l hℳ B P := by
  obtain ⟨s, t, hs, ht, hp⟩ := hP
  exact pair_l hℳ hBase (pair_l hℳ hBase hX hX hs) (pair_l hℳ hBase hX hY ht) hp

def closure_m {Γ Δ : SortContext ℒ} (B X Y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here))
    (pair_m (up X) (up Y) (.bvar .here))

theorem closure_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (quotient_l hℳ) Γ Δ) (B X Y : Term ℒ Γ Δ .set) :
    (closure_m B X Y).satisfies η ↔ ∃ P,
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) P ∧
        SecondOrderPairObjects.pair_l hℳ (X.eval η) (Y.eval η) P := by
  simp only [closure_m, Formula.satisfies, PowerlessRelativeHierarchySemantics.class_formula_l K,
    SecondOrderObjectSyntax.pair_l hℳ, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m : Formula ℒ [] [.set, .set, .set] :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m (.fvar .here)) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m (.fvar .here) (.fvar (.there .here))) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m (.fvar .here) (.fvar (.there (.there .here))))
        (closure_m (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here))))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) : sentence_m.TrueIn (quotient_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hBase hX hY
  have hBase' := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ η (.fvar .here)).mp hBase
  have hX' := (PowerlessRelativeHierarchySemantics.class_formula_l K η (.fvar .here) (.fvar (.there .here))).mp hX
  have hY' := (PowerlessRelativeHierarchySemantics.class_formula_l K η (.fvar .here) (.fvar (.there (.there .here)))).mp hY
  obtain ⟨P, hP⟩ := SecondOrderPairObjects.pair_exists_l hℳ (η.freeVal (.there .here)) (η.freeVal (.there (.there .here)))
  exact (closure_formula_l K η (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))).mpr
    ⟨P, pair_l hℳ hBase' hX' hY' hP, hP⟩

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassPair
