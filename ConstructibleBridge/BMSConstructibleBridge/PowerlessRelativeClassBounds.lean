import BMSConstructibleBridge.PowerlessRelativeLevelClosure
import BMSConstructibleBridge.PowerlessRelativeLeastStage

/-! # 两个类参数的共同层界

仅用序数比较和层单调性寻找有限共同界，不把两个参数的界推广成任意集合
族的 Collection。最小出现阶段的上界比较亦在 Prop 中保留，不抽取秩函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassBounds

open Logic FirstOrder PowerlessBMSQuotientCoding SecondOrderObjectSyntax
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private abbrev quotient_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) := SecondOrderQuotient.structure_l hℳ

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

theorem common_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {B X Y : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hX : PowerlessRelativeClassCorrespondence.member_l hℳ B X)
    (hY : PowerlessRelativeClassCorrespondence.member_l hℳ B Y) :
    ∃ a c, level_l hℳ B a c ∧ mem_l hℳ X c ∧ mem_l hℳ Y c := by
  obtain ⟨a, c, hc, hXc⟩ := hX
  obtain ⟨b, d, hd, hYd⟩ := hY
  rcases SecondOrderOrdinalComparison.compare_l hℳ
    (PowerlessRelativeLevelClosure.ordinal_l hℳ hc) (PowerlessRelativeLevelClosure.ordinal_l hℳ hd) with h | h | h
  · subst b
    have hcd := PowerlessRelativeHierarchyAgreement.level_unique_l hℳ hc hd
    exact ⟨a, c, hc, hXc, hcd.symm ▸ hYd⟩
  · exact ⟨b, d, hd, PowerlessRelativeLevelClosure.subset_l hℳ hBase h hc hd X hXc, hYd⟩
  · exact ⟨a, c, hc, hXc, PowerlessRelativeLevelClosure.subset_l hℳ hBase h hd hc Y hYd⟩

theorem rank_bound_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {B X a b c : type_l hℳ}
    (ha : PowerlessRelativeLeastStage.rank_l hℳ B X a) (hc : level_l hℳ B b c) (hXc : mem_l hℳ X c) :
    a = b ∨ mem_l hℳ a b := by
  rcases SecondOrderOrdinalComparison.compare_l hℳ
    (PowerlessRelativeLeastStage.ordinal_l hℳ ha.1) (PowerlessRelativeLevelClosure.ordinal_l hℳ hc) with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact False.elim (ha.2 b h ⟨c, hc, hXc⟩)

def bound_m {Γ Δ : SortContext ℒ} (B X Y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <|
    .conj (PowerlessRelativeHierarchySyntax.level_m (up (up B)) (.bvar (.there .here)) (.bvar .here)) <|
      .conj (member_m (up (up X)) (.bvar .here)) (member_m (up (up Y)) (.bvar .here))

theorem bound_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (quotient_l hℳ) Γ Δ) (B X Y : Term ℒ Γ Δ .set) :
    (bound_m B X Y).satisfies η ↔ ∃ a c, level_l hℳ (B.eval η) a c ∧
      mem_l hℳ (X.eval η) c ∧ mem_l hℳ (Y.eval η) c := by
  simp only [bound_m, Formula.satisfies, PowerlessRelativeHierarchySemantics.level_formula_l K,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m : Formula ℒ [] [.set, .set, .set] :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m (.fvar .here)) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m (.fvar .here) (.fvar (.there .here))) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m (.fvar .here) (.fvar (.there (.there .here))))
        (bound_m (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here))))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) : sentence_m.TrueIn (quotient_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hBase hX hY
  have hBase' := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ η (.fvar .here)).mp hBase
  have hX' := (PowerlessRelativeHierarchySemantics.class_formula_l K η (.fvar .here) (.fvar (.there .here))).mp hX
  have hY' := (PowerlessRelativeHierarchySemantics.class_formula_l K η (.fvar .here) (.fvar (.there (.there .here)))).mp hY
  exact (bound_formula_l K η (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))).mpr
    (common_l hℳ hBase' hX' hY')

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassBounds
