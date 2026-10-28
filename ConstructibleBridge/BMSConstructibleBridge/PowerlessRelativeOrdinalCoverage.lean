import BMSConstructibleBridge.PowerlessRelativeLevelClosure
import BMSConstructibleBridge.SecondOrderMemberDefOrdinal

/-! # 相对层包含序数初段及相对类覆盖全部序数

使用实际纯公式的内部集合归纳，不对模型序数作宿主归纳。后继步把前驱
序数作为传递母集的有界可定义切片加入 Def；极限步由无最大元及层单调性
取得覆盖。最终两条纯集合闭句均回传原 Z₂，不加入 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeOrdinalCoverage

open Logic FirstOrder PowerlessBMSQuotientCoding SecondOrderObjectSyntax
open SecondOrderQuotient (type_l mk_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private abbrev quotient_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) := SecondOrderQuotient.structure_l hℳ

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

theorem level_exists_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {B a : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (ha : SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (quotient_l hℳ)) a) :
    ∃ c, level_l hℳ B a c := by
  obtain ⟨W, hW, rfl, hTrans⟩ := PowerlessRelativeHierarchyDerives.base_code_l hℳ B hBase
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ a
  obtain ⟨C, hC⟩ := SecondOrderRelativeLevel.exists_l hℳ W hW hTrans A ha
  exact ⟨mk_l hℳ C, PowerlessRelativeLevelCorrespondence.forward_l hℳ hTrans hC⟩

def point_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B a : type_l hℳ) : Prop :=
  ∀ c, level_l hℳ B a c → ∀ x, mem_l hℳ x a → mem_l hℳ x c

def point_m {Γ Δ : SortContext ℒ} (B a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (PowerlessRelativeHierarchySyntax.level_m (up B) (up a) (.bvar .here)) <|
    .forallE .set <| .imp (member_m (.bvar .here) (up (up a)))
      (member_m (.bvar .here) (.bvar (.there .here)))

theorem point_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (quotient_l hℳ) Γ Δ) (B a : Term ℒ Γ Δ .set) :
    (point_m B a).satisfies η ↔ point_l hℳ (B.eval η) (a.eval η) := by
  simp only [point_m, Formula.satisfies, PowerlessRelativeHierarchySemantics.level_formula_l K,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem step_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {B a : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hPast : ∀ b, mem_l hℳ b a → point_l hℳ B b) : point_l hℳ B a := by
  intro c hc
  have ha := PowerlessRelativeLevelClosure.ordinal_l hℳ hc
  obtain ⟨W, hW, rfl, hTrans⟩ := PowerlessRelativeHierarchyDerives.base_code_l hℳ B hBase
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ a
  obtain ⟨C, rfl⟩ := SecondOrderQuotient.surj_l hℳ c
  have hC := PowerlessRelativeLevelCorrespondence.reverse_l hℳ hTrans hc
  rcases SecondOrderOrdinalCases.cases_l hℳ A ha with hZero | ⟨P, hSucc⟩ | ⟨_, hLimit⟩
  · intro x hx
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    exact False.elim (hZero X hx)
  · have hpA : mem_l hℳ (mk_l hℳ P) (mk_l hℳ A) :=
      (hSucc P).mpr (Or.inr (SecondOrderGraph.refl_l hℳ P))
    have hp : SetTheory.Structure.IsOrdinal
        (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (quotient_l hℳ)) (mk_l hℳ P) := by
      apply SetTheory.Structure.IsOrdinal.mem ha
      exact hpA
    obtain ⟨D, hD⟩ := SecondOrderRelativeLevel.exists_l hℳ W hW hTrans P hp
    have hPureD := PowerlessRelativeLevelCorrespondence.forward_l hℳ hTrans hD
    have hpSubset := hPast (mk_l hℳ P) hpA (mk_l hℳ D) hPureD
    have hDef := SecondOrderRelativeLevelSuccessor.value_l hℳ hSucc hD hC
    have hDT := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hPureD
    have hpC := SecondOrderMemberDefOrdinal.member_l hℳ hDef hDT hp hpSubset
    intro x hx
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    rcases (hSucc X).mp hx with hxP | hXP
    · exact SecondOrderMemberDefProperties.contains_l hℳ hDef (fun y z hy hz => hDT y hy z hz)
        (mk_l hℳ X) (hpSubset (mk_l hℳ X) hxP)
    · exact (SecondOrderGraph.mem_congr_l hℳ hXP (SecondOrderGraph.refl_l hℳ C)).mpr hpC
  · intro x hx
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    obtain ⟨Y, hyA, hxY⟩ := hLimit X hx
    have hy : SetTheory.Structure.IsOrdinal
        (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (quotient_l hℳ)) (mk_l hℳ Y) := by
      apply SetTheory.Structure.IsOrdinal.mem ha
      exact hyA
    obtain ⟨d, hd⟩ := level_exists_l hℳ hBase hy
    exact PowerlessRelativeLevelClosure.subset_l hℳ (a := mk_l hℳ Y) (b := mk_l hℳ A)
      (c := d) (d := mk_l hℳ C) hBase hyA hd hc (mk_l hℳ X)
      (hPast (mk_l hℳ Y) hyA d hd (mk_l hℳ X) hxY)

theorem covered_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (K : source_coding_l hℳ)
    {B : type_l hℳ} (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    ∀ a, point_l hℳ B a := by
  let φ : Formula ℒ [] [.set, .set] := point_m (.fvar (.there .here)) (.fvar .here)
  let η : Env (quotient_l hℳ) [] [.set] := Env.empty (M := quotient_l hℳ) |>.pushFree B
  have hRead a : φ.satisfies (η.pushFree a) ↔ point_l hℳ B a := point_formula_l K _ _ _
  have hAll := PowerlessWeakSetInduction.induction_l (SecondOrderWeakSetTheory.models_l hℳ) φ η
    (fun a ih => (hRead a).mpr (step_l hℳ hBase (fun b hb => (hRead b).mp (ih b hb))))
  exact fun a => (hRead a).mp (hAll a)

theorem class_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (K : source_coding_l hℳ)
    {B a : type_l hℳ} (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (ha : SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (quotient_l hℳ)) a) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B a := by
  obtain ⟨c, hc⟩ := level_exists_l hℳ hBase ha
  obtain ⟨b, d, _, hd, hDef⟩ := PowerlessRelativeLevelClosure.successor_exists_l hℳ hBase hc
  exact ⟨b, d, hd, SecondOrderMemberDefOrdinal.member_l hℳ hDef
    (PowerlessRelativeLevelClosure.transitive_l hℳ hBase hc) ha (covered_l hℳ K hBase a c hc)⟩

def coverage_schema_m : Formula ℒ [] [.set] :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m (.fvar .here)) <|
    .forallE .set <| point_m (.fvar .here) (.bvar .here)

def coverage_sentence_m : Sentence ℒ := Metatheory.Formula.forall_close coverage_schema_m

def class_schema_m : Formula ℒ [] [.set, .set] :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m (.fvar .here)) <|
    .imp (PowerlessRelativeHierarchySyntax.ordinal_m (.fvar (.there .here)))
      (PowerlessRelativeHierarchySyntax.class_m (.fvar .here) (.fvar (.there .here)))

def class_sentence_m : Sentence ℒ := Metatheory.Formula.forall_close class_schema_m

theorem coverage_models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    coverage_sentence_m.TrueIn (quotient_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hBase a
  have hBase' := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ η (.fvar .here)).mp hBase
  exact (point_formula_l K (η.pushBound a) (.fvar .here) (.bvar .here)).mpr (covered_l hℳ K hBase' a)

theorem class_models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    class_sentence_m.TrueIn (quotient_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hBase ha
  have hBase' := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ η (.fvar .here)).mp hBase
  have ha' := (PowerlessRelativeHierarchySemantics.ordinal_formula_l η (.fvar (.there .here))).mp ha
  exact (PowerlessRelativeHierarchySemantics.class_formula_l K η (.fvar .here) (.fvar (.there .here))).mpr
    (class_l hℳ K hBase' ha')

theorem coverage_derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m coverage_sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => coverage_models_l hℳ)

theorem class_derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m class_sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => class_models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeOrdinalCoverage
