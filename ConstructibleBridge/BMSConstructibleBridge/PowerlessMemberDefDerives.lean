import BMSConstructibleBridge.PowerlessMemberDefSemantics
import BMSConstructibleBridge.SecondOrderAxioms

/-! # 原 Z₂ 推导核中的纯 Def 存在唯一性

隐藏 ω 与空对象的唯一证书，取得只带两个集合参数的纯关系。回传的结论
是同一图翻译在原 Z₂ 中的正式可推导性；它不是 BMS 良序性的终局定理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberDefDerives

open Logic FirstOrder PowerlessBMSQuotientCoding

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

theorem formula_l (C : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (X Y : Term ℒ Γ Δ .set) :
    (PowerlessMemberDefSyntax.global_m X Y).satisfies η ↔
      SecondOrderMemberDef.spec_l hℳ (X.eval η) (Y.eval η) := by
  simp only [PowerlessMemberDefSyntax.global_m, Formula.satisfies,
    SecondOrderOmegaSyntax.omega_l, SecondOrderObjectSyntax.member_m, Arguments.eval,
    Term.eval]
  constructor
  · rintro ⟨w, z, hω, hz, hDef⟩
    have hw : w = C.omega := SecondOrderOmega.unique_l hℳ hω C.omega_spec
    have he : z = (numberCode_l C (SecondOrderModel.zero_l ℳ)).val := by
      apply SecondOrderQuotient.ext_l hℳ
      intro x
      exact iff_of_false (hz x) (PowerlessBMSQuotientSuccessor.zero_l C x)
    have h := (PowerlessMemberDefSemantics.formula_l C ((η.pushBound w).pushBound z)
      (.bvar (.there .here)) (.bvar .here) (up (up X)) (up (up Y)) hw he).mp hDef
    simpa only [up, Term.eval_weakenBound] using h
  · intro h
    refine ⟨C.omega, (numberCode_l C (SecondOrderModel.zero_l ℳ)).val, C.omega_spec,
      PowerlessBMSQuotientSuccessor.zero_l C, ?_⟩
    apply (PowerlessMemberDefSemantics.formula_l C
      ((η.pushBound C.omega).pushBound (numberCode_l C (SecondOrderModel.zero_l ℳ)).val)
      (.bvar (.there .here)) (.bvar .here) (up (up X)) (up (up Y)) rfl rfl).mpr
    simpa only [up, Term.eval_weakenBound] using h

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    PowerlessMemberDefSyntax.total_unique_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨C⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  intro X
  obtain ⟨Y, hY, hUnique⟩ := SecondOrderMemberDef.exists_l hℳ X
  refine ⟨Y, (formula_l C _ (.bvar (.there .here)) (.bvar .here)).mpr hY, ?_⟩
  intro Z hZ
  exact hUnique Z ((formula_l C _ (.bvar (.there (.there .here))) (.bvar .here)).mp hZ)

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m PowerlessMemberDefSyntax.total_unique_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms formula_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberDefDerives
