import BMSConstructibleBridge.PowerlessRelativeLimitClosure

/-! # 固定极限层闭包的原 Z₂ 推导

对象句显式带传递基集、实际层值与非零极限条件。配对、并集的存在来自
原图商构造，其属于给定层的证明来自严格较早层中的 Def 切片。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitClosureDerives

open Logic FirstOrder SecondOrderObjectSyntax PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySyntax (up)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

def union_m {Γ Δ : SortContext ℒ} (X U : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.iff (member_m (.bvar .here) (up U))
    (.existsE .set (.conj (member_m (.bvar .here) (up (up X)))
      (member_m (.bvar (.there .here)) (.bvar .here)))))

theorem union_formula_l {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (X U : Term ℒ Γ Δ .set) :
    (union_m X U).satisfies η ↔ ∀ w, mem_l hℳ w (U.eval η) ↔
      ∃ y, mem_l hℳ y (X.eval η) ∧ mem_l hℳ w y := by
  simp only [union_m, Formula.satisfies, member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def closure_m {Γ Δ : SortContext ℒ} (C : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ := .conj
  (.forallE .set (.forallE .set (.imp
    (.conj (member_m (.bvar (.there .here)) (up (up C))) (member_m (.bvar .here) (up (up C))))
    (.existsE .set (.conj (member_m (.bvar .here) (up (up (up C))))
      (pair_m (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)))))))
  (.forallE .set (.imp (member_m (.bvar .here) (up C))
    (.existsE .set (.conj (member_m (.bvar .here) (up (up C)))
      (union_m (.bvar (.there .here)) (.bvar .here))))))

theorem closure_formula_l {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (C : Term ℒ Γ Δ .set) :
    (closure_m C).satisfies η ↔
      (∀ X Y, mem_l hℳ X (C.eval η) ∧ mem_l hℳ Y (C.eval η) →
        ∃ P, mem_l hℳ P (C.eval η) ∧ SecondOrderPairObjects.pair_l hℳ X Y P) ∧
      (∀ X, mem_l hℳ X (C.eval η) → ∃ U, mem_l hℳ U (C.eval η) ∧
        ∀ w, mem_l hℳ w U ↔ ∃ y, mem_l hℳ y X ∧ mem_l hℳ w y) := by
  simp only [closure_m, Formula.satisfies, pair_l hℳ, union_formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m : Formula ℒ [] [.set, .set, .set] :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m (.fvar .here)) <|
    .imp (PowerlessRelativeHierarchySyntax.level_m (.fvar .here) (.fvar (.there .here))
      (.fvar (.there (.there .here)))) <|
      .imp (PowerlessRelativeHierarchySyntax.limit_m (.fvar (.there .here)))
        (closure_m (.fvar (.there (.there .here))))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hBase hC hLimit
  have hBase' := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ η (.fvar .here)).mp hBase
  have hC' := (PowerlessRelativeHierarchySemantics.level_formula_l K η
    (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))).mp hC
  have hLimit' := (PowerlessRelativeHierarchySemantics.limit_formula_l
    (hℳ := hℳ) η (.fvar (.there .here))).mp hLimit
  apply (closure_formula_l (hℳ := hℳ) η (.fvar (.there (.there .here)))).mpr
  constructor
  · rintro X Y ⟨hX, hY⟩
    obtain ⟨P, hP⟩ := SecondOrderPairObjects.pair_exists_l hℳ X Y
    exact ⟨P, PowerlessRelativeLimitClosure.pair_l hℳ hBase' hLimit' hC' hX hY hP, hP⟩
  · intro X hX
    have h := SecondOrderUnion.models_l hℳ
    change ∀ a : type_l hℳ, ∃ u, ∀ z, mem_l hℳ z u ↔ ∃ y, mem_l hℳ y a ∧ mem_l hℳ z y at h
    obtain ⟨U, hU⟩ := h X
    exact ⟨U, PowerlessRelativeLimitClosure.union_l hℳ hBase' hLimit' hC' hX hU, hU⟩

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitClosureDerives
