import BMSConstructibleBridge.SecondOrderComparisonLimitSyntax
import BMSConstructibleBridge.SecondOrderOmegaSyntax
import BMSConstructibleBridge.SecondOrderAxioms
import YesMetaZFC.Automation.ModelClosure

/-! # 任意历史极限行的原 Z₂ 对象总唯一性

只要求内部 ω、零对象和层成员覆盖界。历史 G 不必相容或良序，故该
模式可用于真实递归算子的非法前史。良序保持仍由合法前史不变量提供。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonLimitDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding SecondOrderObjectSyntax
open SecondOrderComparisonLimitSyntax (output_m output_l output_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def total_m {Γ Δ : SortContext ℒ} (ω e C I F G f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .imp (PowerlessRelativeHierarchySyntax.empty_m e) <|
      .imp (SecondOrderWellOrderCoherentUnionDerives.cover_m C I F) <|
        .existsE .set <|
          .conj (output_m (up ω) (up e) (up I) (up F) (up G) (up f) (.bvar .here)) <|
            .forallE .set <|
              .imp (output_m (up (up ω)) (up (up e)) (up (up I)) (up (up F)) (up (up G))
                (up (up f)) (.bvar .here)) (.equal (.bvar .here) (.bvar (.there .here)))

def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] :=
  total_m (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, total_m, Formula.satisfies, omega_formula_l,
    PowerlessRelativeHierarchySyntax.empty_m, SecondOrderWellOrderCoherentUnionDerives.cover_formula_l,
    output_formula_l, member_m, Arguments.eval, up, PowerlessRelativeHierarchySyntax.up,
    Term.eval_weakenBound, Term.eval]
  intro hω he hCover
  have hωEq : η.freeVal .here = K.omega := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  have heEq : η.freeVal (.there .here) = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val :=
    SecondOrderQuotient.ext_l hℳ _ _ (fun x => iff_of_false (he x) (PowerlessBMSQuotientSuccessor.zero_l K x))
  change ∃! W : SecondOrderQuotient.type_l hℳ, output_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
    (η.freeVal .here) (η.freeVal (.there .here)) (η.freeVal (.there (.there (.there .here))))
    (η.freeVal (.there (.there (.there (.there .here)))))
    (η.freeVal (.there (.there (.there (.there (.there .here))))))
    (η.freeVal (.there (.there (.there (.there (.there (.there .here))))))) W
  simpa only [hωEq, heEq] using SecondOrderComparisonLimitSyntax.exists_unique_l K hCover

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonLimitDerives
