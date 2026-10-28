import BMSConstructibleBridge.PowerlessRelativeClassCorrespondence

/-! # 纯层值的传递性及后继闭包

对象语言仍为纯隶属语言，出口为原 Z₂ 中的图翻译推导。基集传递性显式
保留；后继层由实际历史构造，不假设相对并类已经满足收集或选择。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLevelClosure

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mk_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l successor_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private abbrev quotient_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) := SecondOrderQuotient.structure_l hℳ

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

theorem ordinal_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {B a c : type_l hℳ}
    (hc : level_l hℳ B a c) :
    SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (quotient_l hℳ)) a := by
  obtain ⟨A, _, _, hA, haA, _, _⟩ := hc
  apply SetTheory.Structure.IsOrdinal.mem hA
  exact haA

theorem transitive_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {B a c : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hc : level_l hℳ B a c) : ∀ x, mem_l hℳ x c → ∀ y, mem_l hℳ y x → mem_l hℳ y c := by
  obtain ⟨W, hW, rfl, hTrans⟩ := PowerlessRelativeHierarchyDerives.base_code_l hℳ B hBase
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ a
  obtain ⟨C, rfl⟩ := SecondOrderQuotient.surj_l hℳ c
  have hC := PowerlessRelativeLevelCorrespondence.reverse_l hℳ hTrans hc
  intro x hx y hy
  obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
  obtain ⟨Y, rfl⟩ := SecondOrderQuotient.surj_l hℳ y
  exact SecondOrderRelativeLevelProperties.transitive_l hℳ hC X Y hx hy

theorem base_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {B a c : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hc : level_l hℳ B a c) : ∀ x, mem_l hℳ x B → mem_l hℳ x c := by
  obtain ⟨W, hW, rfl, hTrans⟩ := PowerlessRelativeHierarchyDerives.base_code_l hℳ B hBase
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ a
  obtain ⟨C, rfl⟩ := SecondOrderQuotient.surj_l hℳ c
  have hC := PowerlessRelativeLevelCorrespondence.reverse_l hℳ hTrans hc
  intro x hx
  obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
  exact SecondOrderRelativeLevelProperties.base_l hℳ hC X hx

theorem class_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {B a c : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hc : level_l hℳ B a c) : PowerlessRelativeClassCorrespondence.member_l hℳ B c := by
  have ha := ordinal_l hℳ hc
  obtain ⟨W, hW, rfl, hTrans⟩ := PowerlessRelativeHierarchyDerives.base_code_l hℳ B hBase
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ a
  obtain ⟨C, rfl⟩ := SecondOrderQuotient.surj_l hℳ c
  have hC := PowerlessRelativeLevelCorrespondence.reverse_l hℳ hTrans hc
  exact (PowerlessRelativeClassCorrespondence.iff_l hℳ hTrans C).mpr
    (SecondOrderRelativeClass.level_l hℳ W hW hTrans A C ha hC)

theorem successor_exists_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {B a c : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hc : level_l hℳ B a c) :
    ∃ b d, successor_l hℳ a b ∧ level_l hℳ B b d ∧ SecondOrderMemberDef.spec_l hℳ c d := by
  have ha := ordinal_l hℳ hc
  obtain ⟨W, hW, rfl, hTrans⟩ := PowerlessRelativeHierarchyDerives.base_code_l hℳ B hBase
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ a
  obtain ⟨C, rfl⟩ := SecondOrderQuotient.surj_l hℳ c
  have hC := PowerlessRelativeLevelCorrespondence.reverse_l hℳ hTrans hc
  obtain ⟨A', hA', _, hSucc⟩ := SecondOrderOrdinalSuccessor.exists_l hℳ A ha
  obtain ⟨C', hC'⟩ := SecondOrderRelativeLevel.exists_l hℳ W hW hTrans A' hA'
  refine ⟨mk_l hℳ A', mk_l hℳ C', ?_, PowerlessRelativeLevelCorrespondence.forward_l hℳ hTrans hC',
    SecondOrderRelativeLevelSuccessor.value_l hℳ hSucc hC hC'⟩
  intro x
  obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
  exact (hSucc X).trans (or_congr Iff.rfl (SecondOrderQuotient.eq_iff_l hℳ X A).symm)

theorem members_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {B a b c d : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hab : mem_l hℳ a b) (hc : level_l hℳ B a c) (hd : level_l hℳ B b d) : mem_l hℳ c d := by
  obtain ⟨W, hW, rfl, hTrans⟩ := PowerlessRelativeHierarchyDerives.base_code_l hℳ B hBase
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ a
  obtain ⟨A', rfl⟩ := SecondOrderQuotient.surj_l hℳ b
  obtain ⟨C, rfl⟩ := SecondOrderQuotient.surj_l hℳ c
  obtain ⟨D, rfl⟩ := SecondOrderQuotient.surj_l hℳ d
  exact SecondOrderRelativeLevelMonotonicity.members_l hℳ
    (SecondOrderGraph.refl_l hℳ ⟨W, SecondOrderModel.zero_l ℳ, hW⟩) hab
    (PowerlessRelativeLevelCorrespondence.reverse_l hℳ hTrans hc)
    (PowerlessRelativeLevelCorrespondence.reverse_l hℳ hTrans hd)

theorem subset_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {B a b c d : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hab : mem_l hℳ a b) (hc : level_l hℳ B a c) (hd : level_l hℳ B b d) :
    ∀ x, mem_l hℳ x c → mem_l hℳ x d := by
  intro x hx
  exact transitive_l hℳ hBase hd c (members_l hℳ hBase hab hc hd) x hx

def closure_m {Γ Δ : SortContext ℒ} (B a c : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelativeHierarchyDerives.transitive_m c) <|
    .conj (PowerlessRelativeHierarchySyntax.class_m B c) <|
      .conj (.forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up B))
        (SecondOrderObjectSyntax.member_m (.bvar .here) (up c))) <|
        .existsE .set <| .existsE .set <|
          .conj (PowerlessRelativeHierarchySyntax.successor_m (up (up a)) (.bvar (.there .here))) <|
            .conj (PowerlessRelativeHierarchySyntax.level_m (up (up B)) (.bvar (.there .here)) (.bvar .here))
              (PowerlessMemberDefSyntax.global_m (up (up c)) (.bvar .here))

theorem closure_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (quotient_l hℳ) Γ Δ) (B a c : Term ℒ Γ Δ .set) :
    (closure_m B a c).satisfies η ↔
      (∀ x, mem_l hℳ x (c.eval η) → ∀ y, mem_l hℳ y x → mem_l hℳ y (c.eval η)) ∧
        PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (c.eval η) ∧
          (∀ x, mem_l hℳ x (B.eval η) → mem_l hℳ x (c.eval η)) ∧
            ∃ b d, successor_l hℳ (a.eval η) b ∧ level_l hℳ (B.eval η) b d ∧
              SecondOrderMemberDef.spec_l hℳ (c.eval η) d := by
  simp only [closure_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ,
    PowerlessRelativeHierarchySemantics.class_formula_l K, PowerlessRelativeHierarchySemantics.successor_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K, PowerlessMemberDefDerives.formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m : Formula ℒ [] [.set, .set, .set] :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m (.fvar .here)) <|
    .imp (PowerlessRelativeHierarchySyntax.level_m (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here))))
      (closure_m (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here))))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) : sentence_m.TrueIn (quotient_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hBase hc
  have hBase' := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ η (.fvar .here)).mp hBase
  have hc' := (PowerlessRelativeHierarchySemantics.level_formula_l K η
    (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))).mp hc
  exact (closure_formula_l K η (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))).mpr
    ⟨transitive_l hℳ hBase' hc', class_l hℳ hBase' hc', base_l hℳ hBase' hc', successor_exists_l hℳ hBase' hc'⟩

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLevelClosure
